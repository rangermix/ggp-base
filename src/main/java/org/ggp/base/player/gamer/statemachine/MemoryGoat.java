package org.ggp.base.player.gamer.statemachine;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadPoolExecutor;

import org.apache.lucene.util.OpenBitSet;
import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.ThreadStateMachine;
import org.ggp.base.util.statemachine.XStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MemoryGoat extends XStateMachineGamer {
	protected Player p;
	private XStateMachine machine;
	private List<Role> roles;
	private int self_index, num_threads;
	private volatile int depthCharges, last_depthCharges;
	private long finishBy;
	private long startedAt;
	private int num_roots;
	private volatile XNodeLight[] roots;
	private volatile XNodeLight[] rootsAbsolute;
	private volatile XNodeLight rootSavedAbsolute;
	private volatile XNodeLight rootSaved;
	private List<XNodeLight> path;
	private CompletionService<Struct> executor;
	private ThreadPoolExecutor thread_pool;
	private Thread thread;
	private ThreadStateMachine[] thread_machines;
	private ThreadStateMachine background_machine;
	private ThreadStateMachine solver_machine;
	private volatile int num_charges, num_per;
	private Map<OpenBitSet, Set<XNodeLight>> graph;
	private volatile double total_background = 0;
	private volatile double total_threadpool = 0;
	private volatile int loops = 0;
	private volatile int play_loops = 0;
	private volatile double sum_x = 0;
	private volatile double sum_x2 = 0;
	private volatile int n = 0;

	private volatile double C_CONST = 50;
	private volatile double EPSILON = .1;
	private Random rand = new Random();

	protected List<XNodeLight> matchPath;


	public class Struct {
		public double[] v;
		public List<XNodeLight> p;
		public int n;

		public Struct(double[] val, List<XNodeLight> arr, int num) {
			this.v = val;
			this.p = arr;
			this.n = num;
		}
	}

	@Override
	public XStateMachine getInitialStateMachine() {
		XStateMachine machine = loadStateMachine();
		if (machine == null) {
			return new XStateMachine();
		}
		return machine;
	}

	@Override
	public void stateMachineMetaGame(long timeout) throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException, InterruptedException, ExecutionException {
		initialize(timeout);

		int num_rests = (int) ((finishBy - System.currentTimeMillis()) / 1000);
		if (num_rests < 0) {
			return;
		}
		for (int i = 0; i < num_rests; ++i) {
			Thread.sleep(1000);
			double avg_back = total_background/loops;
			double avg_threadpool = total_threadpool/play_loops;
			double num = 10 * num_threads * (avg_back/avg_threadpool);
			num_per = (int) num;
			if (num_per < 1) num_per = 1;
		}
		System.out.println("C_CONST: " + C_CONST);
		System.out.println("Depth Charges: " + depthCharges);
		System.out.println("Avg Background: " + total_background/loops);
		System.out.println("Avg Threadpool: " + total_threadpool/play_loops);
		System.out.println("Number of playouts per thread: " + num_per);
		last_depthCharges = 0;
	}

	protected void initialize(long timeout) throws MoveDefinitionException, TransitionDefinitionException, InterruptedException {
		graph = new HashMap<>();
		matchPath = new ArrayList<XNodeLight>();
		num_roots = 4;

		machine = getStateMachine();
		roles = machine.getRoles();
		self_index = roles.indexOf(getRole());

		//lets load the tree here
		rootSavedAbsolute = loadTree();
		System.out.println("Number of loaded nodes: " + XNodeLight.nodeCount);

		rootsAbsolute = new XNodeLight[num_roots+1];
		roots = new XNodeLight[num_roots+1];
		for (int i = 0; i < num_roots; ++i) {
			rootsAbsolute[i] = generateXNode(getCurrentState(), roles.size());
			roots[i] = rootsAbsolute[i];
			Expand(roots[i]);
		}


		num_charges = 1;
		num_per = Runtime.getRuntime().availableProcessors();
		num_threads = Runtime.getRuntime().availableProcessors();
		thread_pool = (ThreadPoolExecutor) Executors.newFixedThreadPool(num_threads);
		executor = new ExecutorCompletionService<Struct>(thread_pool);
		thread_machines = new ThreadStateMachine[num_threads];
		for (int i = 0; i < num_threads; ++i) {
			thread_machines[i] = new ThreadStateMachine(machine,self_index);
		}
		background_machine = new ThreadStateMachine(machine,self_index);

		if (rootSavedAbsolute == null) {
			rootSavedAbsolute = generateXNode(getCurrentState(), roles.size());
			Expand(rootSavedAbsolute);
		}
		rootsAbsolute[rootsAbsolute.length-1] = rootSavedAbsolute;
		roots[roots.length-1] = rootSavedAbsolute;

		thread = new Thread(new runMCTS());
		depthCharges = 0;
		last_depthCharges = 0;
		thread.start();

		finishBy = timeout - 3000;
		System.out.println("NumThreads: " + num_threads);
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException, InterruptedException, ExecutionException {
		//More efficient to use Compulsive Deliberation for one player games
		//Use two-player implementation for two player games
		depthCharges = 0;
		total_background = 0;
		total_threadpool = 0;
		loops = 0;
		play_loops = 0;
		System.out.println("Background Depth Charges: " + last_depthCharges);
		finishBy = timeout - 2500;
		startedAt = System.currentTimeMillis();

		return MCTS();
	}

	protected void initializeMCTS() throws MoveDefinitionException, TransitionDefinitionException, InterruptedException {
		OpenBitSet currentState = getCurrentState();

		for (int i = 0; i < roots.length; ++i) {
			if (roots[i] == null) System.out.println("NULL ROOT");
			if (roots[i].state.equals(currentState)) continue;
			boolean found_next = false;
			for (List<Move> jointMove : machine.getLegalJointMoves(roots[i].state)) {
				OpenBitSet nextState = machine.getNextState(roots[i].state, jointMove);
				if (currentState.equals(nextState)) {
					roots[i] = roots[i].children.get(jointMove);
					if (roots[i] == null) System.out.println("NOT IN MAP");
					found_next = true;
					break;
				}
			}
			if (!found_next) {
				System.out.println("ERROR. Current State not in tree");
				roots[i] = generateXNode(currentState, roles.size());
			}
		}

		matchPath.add(roots[roots.length-1]);

		//restart the worst root
		int worstRoot = 0;
		double worstScore = 100.1;
		for (int i=0; i < num_roots; ++i) {
			double utility = roots[i].utility[self_index] / roots[i].updates;
			if (utility < worstScore) {
				worstRoot = i;
				worstScore = utility;
			}
		}
		System.out.println("Restarting Root at index " + worstRoot);
		roots[worstRoot] = generateXNode(currentState, roles.size());
	}

	protected Move MCTS() throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException, InterruptedException, ExecutionException {
		initializeMCTS();
		thread_pool.getQueue().clear();
		//graph.clear();
		int num_rests = (int) ((finishBy - System.currentTimeMillis()) / 1000);
		if (num_rests < 0) {
			return bestMove();
		}
		for (int i = 0; i < num_rests; ++i) {
			Thread.sleep(1000);
			double avg_back = total_background/loops;
			double avg_threadpool = total_threadpool/play_loops;
			double num = 10 * num_threads * (avg_back/avg_threadpool);
			num_per = (int) num;
			if (num_per < 1) num_per = 1;
		}
		System.out.println("C_CONST: " + C_CONST);
		System.out.println("Depth Charges: " + depthCharges);
		System.out.println("Number of Select/Expand Loops " + loops);
		/*System.out.println("Avg Select: " + total_select/loops);
		System.out.println("Avg Expand: " + total_expand/loops);
		System.out.println("Avg Backprop: " + total_backpropagate/depthCharges);
		System.out.println("Avg Playout: " + total_playout/play_loops);*/
		System.out.println("Avg Background: " + total_background/loops);
		System.out.println("Avg Threadpool: " + total_threadpool/play_loops);
		System.out.println("Number of playouts per thread: " + num_per);
		last_depthCharges = 0;
		return bestMove();
	}

	public class solver implements Runnable {
		@Override
		public void run() {

		}
	}

	protected int alphabeta(int player, OpenBitSet state, int alpha, int beta) throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		if (solver_machine.isTerminal(state))
			return solver_machine.getGoal(state, roles.get(self_index));

		List<List<Move>> jointMoves = solver_machine.getLegalJointMoves(state);
		int score = 100;
		if (player == self_index) score = 0;
		int nextPlayer = player + 1;

		if (player == self_index) {
			for (List<Move> jointMove: jointMoves) {
				OpenBitSet nextState = solver_machine.getNextState(state, jointMove);
				int result = alphabeta(nextPlayer % roles.size(), nextState, alpha, beta);
				if (result == 100 ||  result >= beta) return 100;
				if (result > alpha) alpha = result;
				if (result > score) score = result;
				if(System.currentTimeMillis() > finishBy) return 0;
			}
		} else {
			for (List<Move> jointMove: jointMoves) {
				OpenBitSet nextState = solver_machine.getNextState(state, jointMove);
				int result = alphabeta(nextPlayer % roles.size(), nextState, alpha, beta);
				if (result == 0 || score <= alpha) return 0;
				if (result < beta) beta = result;
				if (result < score) score = result;
				if(System.currentTimeMillis() > finishBy) return 0;
			}
		}

		return score;

	}


	public class runMCTS implements Runnable {
		@Override
		public void run() {
			XNodeLight root_thread;
			while (true) {
				double start = System.currentTimeMillis();
				int rand_idx = rand.nextInt(roots.length);
				root_thread = roots[rand_idx];
				path = new ArrayList<XNodeLight>();
				if (rand_idx == num_roots && !matchPath.isEmpty()) {
					path.addAll(matchPath);
				} else {
					path.add(root_thread);
				}
				//double select_start = System.currentTimeMillis();
				try {
					Select(root_thread, path);
				} catch (MoveDefinitionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				//total_select += (System.currentTimeMillis() - select_start);
				XNodeLight n = path.get(path.size() - 1);
				//double expand_start = System.currentTimeMillis();
				try {
					Expand(n, path);
				} catch (MoveDefinitionException | TransitionDefinitionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				n = path.get(path.size() - 1);
				//total_expand += (System.currentTimeMillis() - expand_start);
				// spawn off multiple threads
				executor.submit(new RunMe(n, path, num_per));

				while(true) {
					Future<Struct> f = executor.poll();
					if (f == null) break;
					Struct s = null;
			        try {
						s = f.get();
					} catch (InterruptedException | ExecutionException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
			        //double back_start = System.currentTimeMillis();
			        int num = s.n;
			        Backpropogate(s.v,s.p, num);
			        //total_backpropagate += (System.currentTimeMillis() - back_start);
			        depthCharges += num;
			        last_depthCharges += num;
			    }
				total_background += (System.currentTimeMillis() - start);
				++loops;
			}
		}
	}

	public class RunMe implements Callable<Struct> {
		private XNodeLight node;
		private List<XNodeLight> p;
		private int num;

		public RunMe(XNodeLight n, List<XNodeLight> arr, int number) {
			this.node = n;
			this.p = arr;
			this.num = number;
		}
		@Override
		public Struct call() throws InterruptedException{
			double start = System.currentTimeMillis();
			double[] val = new double[roles.size()];
			double[] curr = null;
			int thread_ind = (int) (Thread.currentThread().getId() % num_threads);
			ThreadStateMachine mac = thread_machines[thread_ind];
			for (int i = 0; i < num; ++i) {
				//double start = System.currentTimeMillis();
				try {
					curr = mac.Playout(node);
				} catch (MoveDefinitionException | TransitionDefinitionException | GoalDefinitionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < roles.size(); ++j) {
					val[j] += curr[j];
				}
				sum_x += curr[self_index];
				sum_x2 += (curr[self_index]*curr[self_index]);
				++n;
				//++play_loops;
				//total_playout += (System.currentTimeMillis() - start);
			}
			++play_loops;
			total_threadpool += (System.currentTimeMillis() - start);
			Struct s = new Struct(val, p, num);
			return s;
	    }
	}

	protected Move bestMove() throws MoveDefinitionException {
		double maxValue = Double.NEGATIVE_INFINITY;
		Move maxMove = roots[roots.length-1].getLegalMoves(machine, self_index)[0];

		for (XNodeLight n : roots) {
			int size = n.getLegalMoves(machine, self_index).length;
			for(int i = 0; i < size; ++i) {
				Move move = n.getLegalMoves(machine, self_index)[i];
				double minValue = Double.POSITIVE_INFINITY;
				double visits = 0;
				for (List<Move> jointMove : n.getLegalJointMoves(machine, self_index).get(move)) {
					XNodeLight succNode = n.children.get(jointMove);
					if (succNode.updates != 0) {
						double nodeValue = succNode.utility[self_index] / succNode.updates;
						if (nodeValue < minValue) {
							visits = succNode.updates;
							minValue = nodeValue;
						}
					}
				}
				System.out.println("Move: " + move + " Value: " + (minValue == Double.POSITIVE_INFINITY ? "N/A" : String.valueOf(minValue)) + " Visits: " + visits);
				if (minValue > maxValue && minValue != Double.POSITIVE_INFINITY) {
					maxValue = minValue;
					maxMove = move;
				}
			}
			System.out.println("--");
		}
		System.out.println(getName() + " Max Move: " + maxMove + " Max Value: " + maxValue);

		return maxMove;
	}

	protected void Backpropogate(double[] val, List<XNodeLight> path, int num) {
		int size = path.size();
		XNodeLight nod = path.get(size - 1);
		for (int i = 0; i < size; ++i) {
			nod = path.get(i);
			for (int j = 0; j < roles.size(); ++j) {
				nod.utility[j] += val[j];
			}
			nod.updates += num;
		}
		double mean_square = sum_x / n;
		mean_square *= mean_square;
		double avg_square = sum_x2 / n;
		if (avg_square > mean_square) C_CONST = Math.sqrt(avg_square - mean_square);
		if (C_CONST < 50) C_CONST = 50;
	}

	protected void Select(XNodeLight n, List<XNodeLight> path) throws MoveDefinitionException {
		while(true) {
			/*System.out.println(roots.toString());
			System.out.println(n);
			System.out.println(n.children);*/
			++n.visits;
			if (background_machine.isTerminal(n.state)) return;
			if (n.children.isEmpty()) return;
			double maxValue = Double.NEGATIVE_INFINITY;
			double parentVal = C_CONST * Math.sqrt(Math.log(n.visits));
			XNodeLight maxChild = null;

			int size = n.getLegalMoves(machine, self_index).length;

			//select a random move with decaying probability
			List<List<Move>> jointMoves = n.getLegalJointMoves(machine, self_index)
										   .get(n.getLegalMoves(machine, self_index)[rand.nextInt(size)]);
			EPSILON = .1 * (finishBy - System.currentTimeMillis()) / (finishBy - startedAt);
			if (rand.nextDouble() < EPSILON) {
				//System.out.println("RANDOM EPSILON SELECT");
				XNodeLight succNode = n.children.get(jointMoves.get(rand.nextInt(jointMoves.size())));
				if (succNode.visits == 0) {
					++succNode.visits;
					path.add(succNode);
					return;
				}
				maxChild = succNode;
				path.add(maxChild);
				n = maxChild;
				continue;
			}

			for(int i = 0; i < size; ++i) {
				Move move = n.getLegalMoves(machine, self_index)[i];

				double minValue = Double.NEGATIVE_INFINITY;
				XNodeLight minChild = null;
				for (List<Move> jointMove : n.getLegalJointMoves(machine, self_index).get(move)) {
					XNodeLight succNode = n.children.get(jointMove);
					if (succNode.visits == 0) {
						++succNode.visits;
						path.add(succNode);
						return;
					}
					double nodeValue = uctMin(succNode, parentVal);

					if (nodeValue > minValue) {
						minValue = nodeValue;
						minChild = succNode;
					}
				}
				minValue = uctMax(minChild, parentVal);
				if (minValue > maxValue) {
					maxValue = minValue;
					maxChild = minChild;
				}
			}
			path.add(maxChild);
			n = maxChild;
		}
	}


	protected double uctMin(XNodeLight n, double parentVisits) {
		double value = 0;

		if (roles.size() > 1) {
			double utility = 0;
			for (int i = 0; i < roles.size(); ++i) {
				if (i == self_index) continue;
				utility += n.utility[i];
			}
			value = utility / (roles.size() - 1) / n.visits;
		}

		return value + (parentVisits / Math.sqrt(n.visits));
	}

	protected double uctMax(XNodeLight n, double parentVisits) {
		double value = n.utility[self_index] / n.visits;
		return value + (parentVisits / Math.sqrt(n.visits));
	}

	protected void Expand(XNodeLight n, List<XNodeLight> path) throws MoveDefinitionException, TransitionDefinitionException {
		if (n.children.isEmpty() && !background_machine.isTerminal(n.state)) {
			List<Move> moves = background_machine.getLegalMoves(n.state, self_index);
			int size = moves.size();
			n.setLegalMoves(moves.toArray(new Move[size]));


			for (int i = 0; i < size; ++i) {
				Move move = n.getLegalMoves(machine, self_index)[i];
				n.getLegalJointMoves(machine, self_index).put(move, new ArrayList<List<Move>>());
			}
			for (List<Move> jointMove: background_machine.getLegalJointMoves(n.state)) {
				OpenBitSet state = background_machine.getNextState(n.state, jointMove);
				//XNodeLight child = graph.get(state);
				XNodeLight child = n.children.get(jointMove);
				if(child == null) {
					child = generateXNode(state, roles.size());
					n.getLegalJointMoves(machine, self_index).get(jointMove.get(self_index)).add(jointMove);
					n.children.put(jointMove, child);
				}

			}
			path.add(n.children.get(background_machine.getRandomJointMove(n.state)));
		} else if (!background_machine.isTerminal(n.state)) {
			System.out.println("ERROR. Tried to expand node that was previously expanded (2)");
		}
	}

	protected void Expand(XNodeLight n) throws MoveDefinitionException, TransitionDefinitionException {//Assume only expand from max node

		if (n.children.isEmpty() && !machine.isTerminal(n.state)) {
			List<Move> moves = machine.getLegalMoves(n.state, self_index);
			int size = moves.size();
			n.setLegalMoves(moves.toArray(new Move[size]));
			for (int i = 0; i < size; ++i) {
				Move move = n.getLegalMoves(machine, self_index)[i];
				n.getLegalJointMoves(machine, self_index).put(move, new ArrayList<List<Move>>());
			}
			for (List<Move> jointMove: machine.getLegalJointMoves(n.state)) {
				OpenBitSet state = machine.getNextState(n.state, jointMove);
				XNodeLight child = n.children.get(jointMove);
				if(child == null) {
					child = generateXNode(state, roles.size());
					n.getLegalJointMoves(machine, self_index).get(jointMove.get(self_index)).add(jointMove);
					n.children.put(jointMove, child);
				}

			}
		} else if (!machine.isTerminal(n.state)) {
			System.out.println("ERROR. Tried to expand node that was previously expanded (1)");
		}
	}

	@Override
	public void stateMachineStop() {
		saveTree();
		//saveGraph();
		saveMachine();
		cleanup();
	}

	@Override
	public void stateMachineAbort() {
		cleanup();
	}

	protected void cleanup() {

		thread_pool.shutdownNow();
		thread.stop();
		XNodeLight.nodeCount = 0;
	}

	protected void saveTree() {
		int numRules = getMatch().getGame().getRules().size();
		String filename = "gametree" + numRules + ".goat";
		try {
            //Saving of object in a file
            FileOutputStream file = new FileOutputStream(filename);
            ObjectOutputStream out = new ObjectOutputStream(file);

            // Method for serialization of object
            //out.writeObject(rootAbsolute);
            out.writeObject(rootSavedAbsolute);

            out.close();
            file.close();

            System.out.println("Saved game tree in " + filename);

        } catch(IOException ex) {
            System.out.println("IOException when writing to file " + filename);
        }
	}

	protected XNodeLight loadTree() {
		int numRules = getMatch().getGame().getRules().size();
		String filename = "gametree" + numRules + ".goat";
		// Deserialization
		XNodeLight savedRoot = null;
        try
        {
            // Reading the object from a file
            FileInputStream file = new FileInputStream(filename);
            ObjectInputStream in = new ObjectInputStream(file);

            // Method for deserialization of object
            savedRoot = (XNodeLight) in.readObject();

            in.close();
            file.close();

            System.out.println("Loaded game tree from " + filename);
        }

        catch(IOException ex)
        {
            System.out.println("IOException when loading from file " + filename);
        }

        catch(ClassNotFoundException ex)
        {
            System.out.println("ClassNotFoundException when loading from file " + filename);
        }
        return savedRoot;
	}

	protected void saveGraph() {
		int numRules = getMatch().getGame().getRules().size();
		String filename = "gamegraph" + numRules + ".goat";
		try {
            //Saving of object in a file
            FileOutputStream file = new FileOutputStream(filename);
            ObjectOutputStream out = new ObjectOutputStream(file);

            // Method for serialization of object
            //out.writeObject(rootAbsolute);
            out.writeObject(graph);

            out.close();
            file.close();

            System.out.println("Saved game graph in " + filename);

        } catch(IOException ex) {
            System.out.println("IOException when writing to file " + filename);
        }
	}

	//construct a new XNode object, while maintaining the graph mapping structure
	protected XNodeLight generateXNode(OpenBitSet state, int numRoles) {
		XNodeLight node = new XNodeLight(state, numRoles);
		Set<XNodeLight> stateNodes = graph.get(state);
		if (stateNodes == null) {
			stateNodes = new HashSet<XNodeLight>();
		}
		stateNodes.add(node);

		return node;
	}

	@SuppressWarnings("unchecked")
	protected Map<OpenBitSet, XNodeLight> loadGraph() {
		int numRules = getMatch().getGame().getRules().size();
		String filename = "gamegraph" + numRules + ".goat";
		// Deserialization
		Map<OpenBitSet, XNodeLight> savedGraph = null;
        try
        {
            // Reading the object from a file
            FileInputStream file = new FileInputStream(filename);
            ObjectInputStream in = new ObjectInputStream(file);

            // Method for deserialization of object
            savedGraph = (Map<OpenBitSet, XNodeLight>) in.readObject();

            in.close();
            file.close();

            System.out.println("Loaded game graph from " + filename);
        }

        catch(IOException ex)
        {
            System.out.println("IOException when loading from file " + filename);
        }

        catch(ClassNotFoundException ex)
        {
            System.out.println("ClassNotFoundException when loading from file " + filename);
        }
        return savedGraph;
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "The Goat Remembers";
	}



}
