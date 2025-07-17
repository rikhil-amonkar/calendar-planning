from z3 import *

def main():
    # Index of friends: 0:Matthew, 1:Margaret, 2:Nancy, 3:Helen, 4:Rebecca, 5:Kimberly, 6:Kenneth
    names = ["Matthew", "Margaret", "Nancy", "Helen", "Rebecca", "Kimberly", "Kenneth"]
    locations = ["Presidio", "Chinatown", "Pacific Heights", "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"]
    durations = [90, 90, 15, 60, 60, 120, 60]  # in minutes
    available_start = [120, 15, 315, 645, 735, 240, 330]  # in minutes from 9:00 AM
    available_end = [720, 585, 480, 780, 795, 450, 540]  # in minutes from 9:00 AM
    travel_start = [14, 9, 7, 14, 7, 21, 23]  # travel from Russian Hill to each location

    # Travel time between locations: 7x7 matrix [from][to]
    travel = [
        [0, 21, 11, 7, 19, 12, 31],
        [19, 0, 10, 20, 8, 23, 22],
        [11, 11, 0, 12, 13, 15, 22],
        [7, 20, 10, 0, 18, 9, 26],
        [17, 12, 12, 18, 0, 25, 26],
        [11, 23, 16, 7, 24, 0, 23],
        [31, 18, 23, 25, 25, 22, 0]
    ]

    # Initialize Z3 solver and variables
    meet = [Bool(f"meet_{i}") for i in range(7)]
    start = [Int(f"start_{i}") for i in range(7)]  # start times in minutes

    s = Solver()

    # Constraint 1: If meeting i is scheduled, it must be within availability
    for i in range(7):
        s.add(Implies(meet[i], And(start[i] >= available_start[i], start[i] + durations[i] <= available_end[i])))

    # Constraint 2: Distinct start times for scheduled meetings
    for i in range(7):
        for j in range(i + 1, 7):
            s.add(Implies(And(meet[i], meet[j]), start[i] != start[j]))

    # Constraint 3: First meeting must account for travel from Russian Hill
    for i in range(7):
        no_earlier = True
        for k in range(7):
            if k != i:
                no_earlier = And(no_earlier, Or(Not(meet[k]), start[k] >= start[i]))
        s.add(Implies(And(meet[i], no_earlier), start[i] >= travel_start[i]))

    # Constraint 4: Consecutive meetings must account for travel time
    for i in range(7):
        for j in range(7):
            if i == j:
                continue
            cond = And(meet[i], meet[j], start[j] > start[i])
            no_between = True
            for k in range(7):
                if k != i and k != j:
                    no_between = And(no_between, Or(Not(meet[k]), Or(start[k] <= start[i], start[k] >= start[j])))
            s.add(Implies(And(cond, no_between), start[j] >= start[i] + durations[i] + travel[i][j]))

    # Maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(7)])
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(total_meetings)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        total = model.evaluate(total_meetings)
        print(f"SOLUTION: We can meet {total} friends.")
        schedule = []
        for i in range(7):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(start[i])
                if isinstance(start_val, IntNumRef):
                    t_val = start_val.as_long()
                else:
                    t_val = start_val
                name = names[i]
                start_minutes = t_val
                end_minutes = start_minutes + durations[i]
                schedule.append((name, start_minutes, end_minutes))
        schedule.sort(key=lambda x: x[1])
        
        for name, start_min, end_min in schedule:
            def format_time(minutes):
                base_hour = 9
                total_hours = minutes // 60
                total_mins = minutes % 60
                hour = base_hour + total_hours
                if hour >= 24:
                    hour -= 24
                ampm = "AM"
                if hour >= 12:
                    ampm = "PM"
                    if hour > 12:
                        hour -= 12
                return f"{hour}:{total_mins:02d}{ampm}"
            
            start_str = format_time(start_min)
            end_str = format_time(end_min)
            print(f"Meet {name} at {locations[i]} from {start_str} to {end_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()