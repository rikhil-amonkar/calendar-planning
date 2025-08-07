from z3 import *

def main():
    # Given parameters
    n = 10
    seq = [0, 0, 0, 1, 0, 1, 0, 1, 0, 0]  # 0: city, 1: trip
    start_day = "Monday"
    min_days = 22
    min_days_start = 7
    n_passengers = 2  # Number of passengers

    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
    start_day_index = days.index(start_day)  # Get index of start day

    s = Solver()

    # Day of week (0-6) and week counter for each event
    d = [Int(f"d_{i}") for i in range(n)]
    w = [Int(f"w_{i}") for i in range(n)]
    
    # Assignment of events to passengers (1 to n_passengers)
    if n_passengers == 1:
        assigned = [1] * n  # All events assigned to passenger 1
    else:
        assigned = [Int(f"assigned_{i}") for i in range(n)]
        for i in range(n):
            s.add(assigned[i] >= 1, assigned[i] <= n_passengers)

    # Basic constraints for days and weeks
    for i in range(n):
        s.add(d[i] >= 0, d[i] <= 6)  # Day must be 0-6
        s.add(w[i] >= 0)              # Week must be non-negative

    # Events in chronological order
    for i in range(n - 1):
        s.add(w[i + 1] >= w[i])  # Weeks non-decreasing
        # In same week: days non-decreasing
        s.add(If(w[i + 1] == w[i], d[i + 1] >= d[i], True))

    # First event on or after start day
    s.add(d[0] >= start_day_index)

    # Trip events must be on weekends (Saturday=5, Sunday=6)
    for i in range(n):
        if seq[i] == 1:  # Trip event
            s.add(Or(d[i] == 5, d[i] == 6))

    # Passenger gap constraints
    if n_passengers == 1:
        # For single passenger: consecutive events <= min_days_start apart
        for i in range(n - 1):
            gap = (d[i + 1] - d[i]) + 7 * (w[i + 1] - w[i])
            s.add(gap <= min_days_start)
    else:
        # For multiple passengers: consecutive events per passenger <= min_days_start
        for p in range(n_passengers):
            p_val = p + 1
            for i in range(n):
                for j in range(i + 1, n):
                    # Check no passenger p events between i and j
                    no_event_between = True
                    for k in range(i + 1, j):
                        no_event_between = And(no_event_between, assigned[k] != p_val)
                    gap = (d[j] - d[i]) + 7 * (w[j] - w[i])
                    constraint = Implies(
                        And(assigned[i] == p_val, assigned[j] == p_val, no_event_between),
                        gap <= min_days_start
                    )
                    s.add(constraint)

    # Total trip duration constraint
    total_days = (d[n - 1] - d[0]) + 7 * (w[n - 1] - w[0])
    s.add(total_days >= min_days)

    # Solve and output results
    if s.check() == sat:
        m = s.model()
        # Use standard model lookup and convert to Python ints
        day_indices = [m[d[i]].as_long() for i in range(n)]
        day_names = [days[idx] for idx in day_indices]
        week_numbers = [m[w[i]].as_long() for i in range(n)]
        
        if n_passengers > 1:
            passenger_assignments = [m[assigned[i]].as_long() for i in range(n)]
        
        print("Event Schedule:")
        print("Day of Week:".ljust(15) + " ".join(f"{day:10}" for day in day_names))
        print("Week Number:".ljust(15) + " ".join(f"{week:10}" for week in week_numbers))
        print("Activity Type:".ljust(15) + " ".join(f"{'trip' if s==1 else 'city':10}" for s in seq))
        
        if n_passengers > 1:
            print("Passenger:".ljust(15) + " ".join(f"{passenger:10}" for passenger in passenger_assignments))
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()