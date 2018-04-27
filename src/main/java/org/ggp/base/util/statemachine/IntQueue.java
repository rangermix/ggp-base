package org.ggp.base.util.statemachine;

import java.io.Serializable;

public class IntQueue implements Serializable {

	private static final long serialVersionUID = 5640934574376106362L;

	private int size;
	private int[] arr;
	private int curr = 0;
	private int next = 0;
	public int num_queued = 0;

	public IntQueue(int s) {
		this.size = s;
		arr = new int[s];
	}

	public void add(int val) {
		arr[curr] = val;
		++curr;
		++num_queued;
	}

	public int remove() {
		--num_queued;
		return arr[next++];
	}

	public boolean isEmpty() {
		return (num_queued == 0);
	}

	public void clear() {
		num_queued = 0;
		curr = 0;
		next = 0;
	}
}
