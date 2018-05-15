package org.ggp.base.player.gamer.statemachine;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
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
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.ThreadStateMachine;
import org.ggp.base.util.statemachine.XStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;


public class X_MCTS_threadpool extends XStateMachineGamer {
	protected Player p;
	private XStateMachine machine;
	private List<Role> roles;
	private int self_index, num_threads;
	private volatile int depthCharges, last_depthCharges;
	private long finishBy;
	private volatile XNode root;
	private List<XNode> path;
	private CompletionService<Struct> executor;
	private ThreadPoolExecutor thread_pool;
	private Thread thread;
	private ThreadStateMachine[] thread_machines;
	private ThreadStateMachine background_machine;
	private ThreadStateMachine solver_machine;
	private volatile int num_charges, num_per;
	private Map<OpenBitSet, XNode> graph;
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

	public class Struct {
		public double v;
		public List<XNode> p;
		public int n;

		public Struct(double val, List<XNode> arr, int num) {
			this.v = val;
			this.p = arr;
			this.n = num;
		}
	}

	@Override
	public XStateMachine getInitialStateMachine() {
		return new XStateMachine();
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
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
		graph = new HashMap<OpenBitSet, XNode>();
		machine = getStateMachine();
		roles = machine.getRoles();
		self_index = roles.indexOf(getRole());
		root = new XNode(getCurrentState());

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
		Expand(root);
		thread = new Thread(new runMCTS());
		depthCharges = 0;
		last_depthCharges = 0;
		thread.start();

		finishBy = timeout - 2500;
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
		return MCTS();
	}

	protected void initializeMCTS() throws MoveDefinitionException, TransitionDefinitionException, InterruptedException {
		OpenBitSet currentState = getCurrentState();
		if (root == null) System.out.println("NULL ROOT");
		if (root.state.equals(currentState)) return;
		for (List<Move> jointMove : machine.getLegalJointMoves(root.state)) {
			OpenBitSet nextState = machine.getNextState(root.state, jointMove);
			if (currentState.equals(nextState)) {
				root = root.children.get(jointMove);
				if (root == null) System.out.println("NOT IN MAP");
				return;
			}
		}
		System.out.println("ERROR. Current State not in tree");
		root = new XNode(currentState);
	}

	protected Move MCTS() throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException, InterruptedException, ExecutionException {
		initializeMCTS();
		thread_pool.getQueue().clear();
		graph.clear();
		int num_rests = (int) ((finishBy - System.currentTimeMillis()) / 1000);
		if (num_rests < 0) {
			return bestMove(root);
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
		return bestMove(root);
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
			XNode root_thread;
			while (true) {
				double start = System.currentTimeMillis();
				root_thread = root;
				path = new ArrayList<XNode>();
				path.add(root_thread);
				//double select_start = System.currentTimeMillis();
				try {
					Select(root_thread, path);
				} catch (MoveDefinitionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				//total_select += (System.currentTimeMillis() - select_start);
				XNode n = path.get(path.size() - 1);
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
		private XNode node;
		private List<XNode> p;
		private int num;

		public RunMe(XNode n, List<XNode> arr, int number) {
			this.node = n;
			this.p = arr;
			this.num = number;
		}
		@Override
		public Struct call() throws InterruptedException{
			double start = System.currentTimeMillis();
			double val = 0;
			double curr = 0;
			int thread_ind = (int) (Thread.currentThread().getId() % num_threads);
			ThreadStateMachine mac = thread_machines[thread_ind];
			for (int i = 0; i < num; ++i) {
				//double start = System.currentTimeMillis();
				try {
					curr = mac.Playout(node)[self_index];
				} catch (MoveDefinitionException | TransitionDefinitionException | GoalDefinitionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				val += curr;
				sum_x += curr;
				sum_x2 += (curr*curr);
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

	protected Move bestMove(XNode n) throws MoveDefinitionException {
		double maxValue = Double.NEGATIVE_INFINITY;
		Move maxMove = n.legalMoves[0];
		int size = n.legalMoves.length;
		for(int i = 0; i < size; ++i) {
			Move move = n.legalMoves[i];
			double minValue = Double.POSITIVE_INFINITY;
			double visits = 0;
			for (List<Move> jointMove : n.legalJointMoves.get(move)) {
				XNode succNode = n.children.get(jointMove);
				if (succNode.updates != 0) {
					double nodeValue = succNode.utility / succNode.updates;
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
		System.out.println(getName() + " Max Move: " + maxMove + " Max Value: " + maxValue);
		return maxMove;
	}

	protected void Backpropogate(double val, List<XNode> path, int num) {
		int size = path.size();
		XNode nod = path.get(size - 1);
		for (int i = 0; i < size; ++i) {
			nod = path.get(i);
			nod.utility += val;
			nod.updates += num;
		}
		double mean_square = sum_x / n;
		mean_square *= mean_square;
		double avg_square = sum_x2 / n;
		if (avg_square > mean_square) C_CONST = Math.sqrt(avg_square - mean_square);
		if (C_CONST < 50) C_CONST = 50;
	}

	protected void Select(XNode n, List<XNode> path) throws MoveDefinitionException {
		while(true) {
			++n.visits;
			if (background_machine.isTerminal(n.state)) return;
			if (n.children.isEmpty()) return;
			double maxValue = Double.NEGATIVE_INFINITY;
			double parentVal = C_CONST * Math.sqrt(Math.log(n.visits));
			XNode maxChild = null;
			int size = n.legalMoves.length;
			for(int i = 0; i < size; ++i) {
				Move move = n.legalMoves[i];
				double minValue = Double.NEGATIVE_INFINITY;
				XNode minChild = null;
				for (List<Move> jointMove : n.legalJointMoves.get(move)) {
					XNode succNode = n.children.get(jointMove);
					if (succNode.visits == 0) {
						++succNode.visits;
						path.add(succNode);
						return;
					}
					double nodeValue = uctMin(succNode, parentVal);

					if (nodeValue > minValue || rand.nextDouble() < EPSILON) {
						minValue = nodeValue;
						minChild = succNode;
					}
				}
				minValue = uctMax(minChild, parentVal);
				if (minValue > maxValue || rand.nextDouble() < EPSILON) {
					maxValue = minValue;
					maxChild = minChild;
				}
			}
			path.add(maxChild);
			n = maxChild;
		}
	}


	protected double uctMin(XNode n, double parentVisits) {
		double value = n.utility / n.visits;
		return -value + (parentVisits / Math.sqrt(n.visits));
	}

	protected double uctMax(XNode n, double parentVisits) {
		double value = n.utility / n.visits;
		return value + (parentVisits / Math.sqrt(n.visits));
	}

	protected void Expand(XNode n, List<XNode> path) throws MoveDefinitionException, TransitionDefinitionException {
		if (n.children.isEmpty() && !background_machine.isTerminal(n.state)) {
			List<Move> moves = background_machine.getLegalMoves(n.state, self_index);
			int size = moves.size();
			if (size < 1) {
				System.out.println("Size less than 1!!!!!!!!!!");
			}
			n.legalMoves = moves.toArray(new Move[size]);
			for (int i = 0; i < size; ++i) {
				Move move = n.legalMoves[i];
				n.legalJointMoves.put(move, new ArrayList<List<Move>>());
			}
			for (List<Move> jointMove: background_machine.getLegalJointMoves(n.state)) {
				OpenBitSet state = background_machine.getNextState(n.state, jointMove);
				XNode child = graph.get(state);
				if(child == null) {
					child = new XNode(state);
					graph.put(state, child);
				}
				n.legalJointMoves.get(jointMove.get(self_index)).add(jointMove);
				n.children.put(jointMove, child);
			}
			path.add(n.children.get(background_machine.getRandomJointMove(n.state)));
		} else if (!background_machine.isTerminal(n.state)) {
			System.out.println("ERROR. Tried to expand node that was previously expanded");
		}
	}

	protected void Expand(XNode n) throws MoveDefinitionException, TransitionDefinitionException {//Assume only expand from max node
		if (n.children.isEmpty() && !machine.isTerminal(n.state)) {
			List<Move> moves = machine.getLegalMoves(n.state, self_index);
			int size = moves.size();
			n.legalMoves = moves.toArray(new Move[size]);
			for (int i = 0; i < size; ++i) {
				Move move = n.legalMoves[i];
				n.legalJointMoves.put(move, new ArrayList<List<Move>>());
			}
			for (List<Move> jointMove: machine.getLegalJointMoves(n.state)) {
				OpenBitSet state = machine.getNextState(n.state, jointMove);
				XNode child = graph.get(state);
				if(child == null) {
					child = new XNode(state);
					graph.put(state, child);
				}
				n.legalJointMoves.get(jointMove.get(self_index)).add(jointMove);
				n.children.put(jointMove, child);
			}
		} else if (!machine.isTerminal(n.state)) {
			System.out.println("ERROR. Tried to expand node that was previously expanded");
		}
	}

	@SuppressWarnings("deprecation")
	@Override
	public void stateMachineStop() {
		GdlPool.drainPool();
		thread_pool.shutdownNow();
		thread.stop();
		GdlPool.drainPool();
	}

	@SuppressWarnings("deprecation")
	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub
		thread_pool.shutdownNow();
		thread.stop();
		GdlPool.drainPool();
	}


	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "X_MCTS_threadpool Player";
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}




}



