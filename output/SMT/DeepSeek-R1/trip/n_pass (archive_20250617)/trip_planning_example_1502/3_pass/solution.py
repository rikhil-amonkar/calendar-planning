from z3 import *

def main():
    # Number of activities
    n_activities = 15
    
    # Define the start and end times for each activity
    start = [Int(f'start_{i}') for i in range(n_activities)]
    end = [Int(f'end_{i}') for i in range(n_activities)]
    
    # Create a solver
    solver = Solver()
    
    # Define segments: groups of 3 consecutive activities
    segments = []
    for i in range(0, n_activities, 3):
        seg = [j for j in range(i, i+3) if j < n_activities]
        segments.append(seg)
    
    # Activity duration: each activity lasts 1 day
    for i in range(n_activities):
        solver.add(end[i] == start[i] + 1)
    
    # First activity starts at day 1
    solver.add(start[0] == 1)
    
    # Constraints within each segment: consecutive activities start on consecutive days
    for seg in segments:
        for j in range(1, len(seg)):
            solver.add(start[seg[j]] == start[seg[j-1]] + 1)
    
    # Constraints between segments: next segment starts 4 days after last activity of previous segment
    for i in range(1, len(segments)):
        last_activity_prev = segments[i-1][-1]
        first_activity_curr = segments[i][0]
        solver.add(start[first_activity_curr] == start[last_activity_prev] + 4)
    
    # Last activity must end at day 27
    solver.add(end[14] == 27)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Print the schedule
        for i in range(n_activities):
            s = model.evaluate(start[i]).as_long()
            e = model.evaluate(end[i]).as_long()
            print(f"Activity {i}: starts at {s}, ends at {e}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()