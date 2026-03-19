import { batch, Signal } from "@preact/signals";
import { MethodState } from "../index.ts";
import { type Data } from "./config.ts";

type State = MethodState<any, Data>;

// Applies a reduction to the current state, and updates the navigation functions
export function applyReduction(
  state: Signal<State>,
  reduce: () => void,
) {
  // Deep clone current state and insert it into the stack below the
  // curent state, and delete all states after the current one
  const currState = state.peek()!;
  const stateClone = structuredClone(currState.stack[currState.idx]);
  currState.stack = currState.stack.slice(0, currState.idx + 1);
  currState.stack.splice(currState.idx, 0, stateClone);
  currState.idx = currState.idx + 1;
  currState.forward = undefined;
  currState.forwardParallel = undefined;

  reduce();

  // Function to go forward to the next state
  const forward = () => {
    const currState = state.peek()!;
    // Move forward one step
    currState.idx = currState.idx + 1;
    // Update other functions
    if (currState.stack.length - 1 === currState.idx) {
      currState.forward = undefined;
      currState.forwardParallel = undefined;
      currState.last = undefined;
    }
    currState.back = back;
    currState.reset = reset;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to go back to the previous state
  const back = () => {
    const currState = state.peek()!;
    // Move back one step
    currState.idx = currState.idx - 1;
    // Update other functions
    if (currState.idx === 0) {
      currState.back = undefined;
      currState.reset = undefined;
    }
    currState.forward = forward;
    currState.last = last;
    currState.data.appliedFinalStep = false;
    currState.data.isFinalStep = false;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to reset to the initial state
  const reset = () => {
    const currState = state.peek()!;
    // Move back all the way to the beginning
    currState.idx = 0;
    // Update other functions
    currState.back = undefined;
    currState.reset = undefined;
    currState.forward = forward;
    currState.last = last;
    currState.data.appliedFinalStep = false;
    currState.data.isFinalStep = false;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Function to go to the last state
  const last = () => {
    const currState = state.peek()!;
    // Move forward all the way to the end
    currState.idx = currState.stack.length - 1;
    // Update other functions
    currState.forward = undefined;
    currState.forwardParallel = undefined;
    currState.last = undefined;
    currState.back = back;
    currState.reset = reset;
    // Trigger state update
    batch(() => {
      state.value = { ...currState };
    });
  };

  // Update functions that are also set to defined values inside `forward` defined above, assuming that `currState.stack.length - 1 === currState.idx`
  currState.back = back;
  currState.reset = reset;

  state.value = { ...currState };
}
