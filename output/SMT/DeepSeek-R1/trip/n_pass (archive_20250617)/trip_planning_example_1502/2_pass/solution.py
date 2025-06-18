from z3 import *

def main():
    # Number of activities
    n_activities = 15
    
    # Travel time between activities
    travel_time = 1
    
    # Define the start and end times for each activity
    start = [Int(f'start_{i}') for i in range(n_activities)]
    end = [Int(f'end_{i}') for i in range(n_activities)]
    
    # Create a solver
    solver = Solver()
    
    # Define segments: groups of 3 consecutive activities
    segments = []
    for i in range(0, n_activities, 3):
        seg = [j for j in range(i, i+3) if j < n_activities]
        segments.append(tuple(seg))
    
    # Constraints for each activity
    for i in range(n_activities):
        # Start and end times must be non-negative
        solver.add(start[i] >= 1)
        solver.add(end[i] >= 1)
        # Duration of each activity is 1 unit
        solver.add(end[i] == start[i] + 1)
    
    # Constraints for consecutive activities within each segment
    for seg in segments:
        for j in range(len(seg) - 1):
            # The end time of the current activity plus travel time must be <= start time of next
            solver.add(end[seg[j]] + travel_time <= start[seg[j+1]])
    
    # Additional constraint: first activity of each segment must start at time 1
    for seg in segments:
        if len(seg) > 0:
            solver.add(start[seg[0]] == 1)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Print the schedule
        for i in range(n_activities):
            print(f"Activity {i}: starts at {model.evaluate(start[i])}, ends at {model.evaluate(end[i])}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()