from z3 import *

def main():
    # Input data with total duration 23 days
    data = {
        "Event1": {"duration": 10, "earliest_start": 0, "latest_end": 30},
        "Event2": {"duration": 8, "earliest_start": 1, "latest_end": 30},
        "Event3": {"duration": 5, "earliest_start": 2, "latest_end": 30}
    }
    
    events = list(data.keys())
    n = len(events)
    
    # Verify total duration is 23 days
    total_duration = sum(data[event]["duration"] for event in events)
    if total_duration != 23:
        print(f"No valid schedule: Total duration must be 23 (actual: {total_duration})")
        return
    
    s = Solver()
    
    # Create schedule variables
    sched = {}
    for event in events:
        start_var = Int(f"start_{event}")
        end_var = Int(f"end_{event}")
        sched[event] = (start_var, end_var)
        
        # Add event constraints
        s.add(start_var >= data[event]["earliest_start"])
        s.add(end_var <= data[event]["latest_end"])
        s.add(end_var == start_var + data[event]["duration"])
    
    # Create arrays for start/end times
    start_arr = Array('start_arr', IntSort(), IntSort())
    end_arr = Array('end_arr', IntSort(), IntSort())
    
    # Map event indices to times
    for idx, event in enumerate(events):
        s.add(start_arr[idx] == sched[event][0])
        s.add(end_arr[idx] == sched[event][1])
    
    # Create sequence variables
    seq = [Int(f"seq_{i}") for i in range(n)]
    s.add(Distinct(seq))
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < n)
    
    # Consecutive event constraints
    for i in range(n-1):
        s.add(end_arr[seq[i]] == start_arr[seq[i+1]])
    
    # Itinerary must start at 0 and end at 23
    s.add(start_arr[seq[0]] == 0)
    s.add(end_arr[seq[n-1]] == 23)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        seq_order = [m.evaluate(seq[i]).as_long() for i in range(n)]
        event_sequence = [events[i] for i in seq_order]
        
        print("Optimal schedule found (23-day itinerary):")
        print("Event sequence:", " -> ".join(event_sequence))
        for event in events:
            start_val = m.evaluate(sched[event][0]).as_long()
            end_val = m.evaluate(sched[event][1]).as_long()
            print(f"{event}: start={start_val}, end={end_val}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()