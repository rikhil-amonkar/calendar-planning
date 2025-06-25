from z3 import *

def main():
    # Sample input data
    data = {
        "Event1": {"duration": 2, "earliest_start": 0, "latest_end": 10},
        "Event2": {"duration": 3, "earliest_start": 1, "latest_end": 12},
        "Event3": {"duration": 1, "earliest_start": 2, "latest_end": 15}
    }
    max_time = 20

    events = list(data.keys())
    n = len(events)
    
    s = Solver()
    
    # Create a schedule dictionary with start and end variables for each event
    sched = {}
    for event in events:
        start_var = Int(f"start_{event}")
        end_var = Int(f"end_{event}")
        sched[event] = (start_var, end_var)
        
        # Add constraints for each event
        s.add(start_var >= data[event]["earliest_start"])
        s.add(end_var <= data[event]["latest_end"])
        s.add(end_var == start_var + data[event]["duration"])
    
    # Create arrays for start and end times
    start_arr = Array('start_arr', IntSort(), IntSort())
    end_arr = Array('end_arr', IntSort(), IntSort())
    
    # Map event indices to their start/end times
    for idx, event in enumerate(events):
        s.add(start_arr[idx] == sched[event][0])
        s.add(end_arr[idx] == sched[event][1])
    
    # Create sequence variables
    seq = [Int(f"seq_{i}") for i in range(n)]
    s.add(Distinct(seq))
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < n)
    
    # Add consecutive event constraints using arrays
    for i in range(n-1):
        s.add(end_arr[seq[i]] == start_arr[seq[i+1]])
    
    # Check and print solution
    if s.check() == sat:
        m = s.model()
        # Get the sequence order
        seq_sol = [m.evaluate(seq[i]).as_long() for i in range(n)]
        event_sequence = [events[i] for i in seq_sol]
        
        print("Optimal schedule found:")
        print("Event sequence:", " -> ".join(event_sequence))
        for event in events:
            start_val = m.evaluate(sched[event][0]).as_long()
            end_val = m.evaluate(sched[event][1]).as_long()
            print(f"{event}: start={start_val}, end={end_val}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()