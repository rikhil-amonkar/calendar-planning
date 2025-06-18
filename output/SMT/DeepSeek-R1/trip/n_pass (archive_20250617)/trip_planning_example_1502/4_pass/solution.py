from z3 import *

def main():
    n_activities = 15
    start = [Int(f'start_{i}') for i in range(n_activities)]
    end = [Int(f'end_{i}') for i in range(n_activities)]
    solver = Solver()
    
    segments = [
        [0, 1, 2],
        [3, 4, 5],
        [6, 7, 8],
        [9, 10, 11],
        [12, 13, 14]
    ]
    
    # Activity duration: each is 1 day
    for i in range(n_activities):
        solver.add(end[i] == start[i] + 1)
    
    # First activity starts at day 1
    solver.add(start[0] == 1)
    
    # Last activity ends at day 27
    solver.add(end[14] == 27)
    
    # Within segments: consecutive activities without gaps
    for seg in segments:
        for j in range(1, len(seg)):
            solver.add(start[seg[j]] == end[seg[j-1]])
    
    # Between segments: 3 travel days between segments
    for i in range(len(segments)-1):
        last_in_prev = segments[i][-1]
        first_in_next = segments[i+1][0]
        solver.add(start[first_in_next] == end[last_in_prev] + 3)
    
    if solver.check() == sat:
        model = solver.model()
        for i in range(n_activities):
            s = model.evaluate(start[i]).as_long()
            e = model.evaluate(end[i]).as_long()
            print(f"Activity {i}: starts at {s}, ends at {e}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()