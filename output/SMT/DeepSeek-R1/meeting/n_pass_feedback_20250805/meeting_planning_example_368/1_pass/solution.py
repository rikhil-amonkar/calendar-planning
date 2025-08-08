import json
from z3 import *

def main():
    # Friend data: names, locations, availability, and durations
    names = ['Joseph', 'Nancy', 'Jason', 'Jeffrey']
    # Travel times from Bayview to each friend's location (in minutes)
    bayview_times = [23, 16, 21, 19]  # Joseph, Nancy, Jason, Jeffrey
    # Minimum meeting durations (in minutes)
    durations = [60, 90, 15, 45]      # Joseph, Nancy, Jason, Jeffrey
    # Availability start times (minutes from 9:00 AM)
    available_start = [-30, 120, 465, 90]  # Joseph, Nancy, Jason, Jeffrey
    # Availability end times (minutes from 9:00 AM)
    available_end = [615, 420, 765, 405]   # Joseph, Nancy, Jason, Jeffrey

    # Travel time matrix between friends: T[i][j] = time from friend i to friend j
    T = [
        [0, 15, 5, 11],   # From Joseph (0) to others
        [13, 0, 15, 17],  # From Nancy (1) to others
        [4, 16, 0, 8],    # From Jason (2) to others
        [10, 17, 7, 0]    # From Jeffrey (3) to others
    ]

    # Pairs of friends (i, j) with i < j
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    # Z3 variables
    meet = [Bool(f'meet_{name}') for name in names]
    s = [Int(f's_{name}') for name in names]  # Start times in minutes from 9:00 AM
    # Order booleans for each pair
    b_vars = [Bool(f'b_{i}_{j}') for (i, j) in pairs]

    # Initialize optimizer
    opt = Optimize()

    # Constraints for each friend
    for i in range(4):
        # If meeting the friend, ensure start time is feasible
        opt.add(Implies(meet[i], s[i] >= bayview_times[i]))
        opt.add(Implies(meet[i], s[i] >= available_start[i]))
        opt.add(Implies(meet[i], s[i] + durations[i] <= available_end[i]))
        # Ensure start time is non-negative
        opt.add(Implies(meet[i], s[i] >= 0))

    # Constraints for each pair of friends
    for idx, (i, j) in enumerate(pairs):
        both_met = And(meet[i], meet[j])
        # Travel time if i before j
        time_i_j = s[i] + durations[i] + T[i][j]
        # Travel time if j before i
        time_j_i = s[j] + durations[j] + T[j][i]
        # Order constraints
        c1 = Implies(b_vars[idx], time_i_j <= s[j])
        c2 = Implies(Not(b_vars[idx]), time_j_i <= s[i])
        opt.add(Implies(both_met, And(c1, c2)))

    # Maximize the number of friends met
    total_met = Sum([If(m, 1, 0) for m in meet])
    opt.maximize(total_met)

    # Solve and get the model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(4):
            if model.eval(meet[i]):
                start_minutes = model.eval(s[i]).as_long()
                # Convert to minutes from midnight (9:00 AM = 540 minutes)
                abs_start = 540 + start_minutes
                hours_start = abs_start // 60
                minutes_start = abs_start % 60
                start_time = f"{hours_start:02d}:{minutes_start:02d}"
                # Calculate end time
                end_minutes = start_minutes + durations[i]
                abs_end = 540 + end_minutes
                hours_end = abs_end // 60
                minutes_end = abs_end % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {'itinerary': itinerary}
    else:
        result = {'itinerary': []}

    # Output the solution
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()