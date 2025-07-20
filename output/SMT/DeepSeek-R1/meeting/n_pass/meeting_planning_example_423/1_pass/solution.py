from z3 import *
import itertools
from datetime import datetime, timedelta

def main():
    friends = ['Jason', 'Melissa', 'Brian', 'Elizabeth', 'Laura']
    locations = [1, 2, 3, 4, 5]  # Corresponding location indices for each friend
    durations = [90, 45, 15, 105, 75]  # Minimum meeting durations in minutes
    available_start = [240, 585, 45, -15, 315]  # Minutes from 9:00 AM
    available_end = [705, 675, 765, 750, 630]  # Minutes from 9:00 AM

    # Travel time matrix: [0:Presidio, 1:Richmond, 2:North Beach, 3:Financial, 4:Golden Gate, 5:Union Square]
    T = [
        [0, 7, 18, 23, 12, 22],
        [7, 0, 17, 22, 9, 21],
        [17, 18, 0, 8, 22, 7],
        [22, 21, 7, 0, 23, 9],
        [11, 7, 24, 26, 0, 22],
        [24, 20, 10, 9, 22, 0]
    ]

    # Try subsets of friends from largest to smallest
    n_friends = 5
    base_time = datetime(2023, 1, 1, 9, 0)  # 9:00 AM base time
    solution_found = False
    result_schedule = []

    for n in range(n_friends, 0, -1):
        for subset in itertools.combinations(range(n_friends), n):
            s = Solver()
            order = [Int(f'order_{i}') for i in range(n)]
            s.add(Distinct(order))
            s.add([And(order[i] >= 0, order[i] < n_friends) for i in range(n)])
            for i in range(n):
                s.add(Or([order[i] == idx for idx in subset]))
            
            start_times = [Int(f'start_{i}') for i in range(n)]
            duration_vars = [Int(f'duration_{i}') for i in range(n)]
            avail_start_vars = [Int(f'avail_start_{i}') for i in range(n)]
            avail_end_vars = [Int(f'avail_end_{i}') for i in range(n)]
            
            for i in range(n):
                for idx in range(n_friends):
                    s.add(If(order[i] == idx, duration_vars[i] == durations[idx], True))
                    s.add(If(order[i] == idx, avail_start_vars[i] == available_start[idx], True))
                    s.add(If(order[i] == idx, avail_end_vars[i] == available_end[idx], True))
            
            # First meeting constraints
            travel_time0 = Int('travel_time0')
            for idx in range(n_friends):
                s.add(If(order[0] == idx, travel_time0 == T[0][locations[idx]], True))
            s.add(start_times[0] >= travel_time0)
            s.add(start_times[0] >= avail_start_vars[0])
            s.add(start_times[0] + duration_vars[0] <= avail_end_vars[0])
            
            # Subsequent meetings
            for i in range(1, n):
                travel_time_i = Int(f'travel_time_{i}')
                for prev_idx in range(n_friends):
                    for curr_idx in range(n_friends):
                        s.add(If(And(order[i-1] == prev_idx, order[i] == curr_idx),
                                  travel_time_i == T[locations[prev_idx]][locations[curr_idx]],
                                  True))
                s.add(start_times[i] >= start_times[i-1] + duration_vars[i-1] + travel_time_i)
                s.add(start_times[i] >= avail_start_vars[i])
                s.add(start_times[i] + duration_vars[i] <= avail_end_vars[i])
            
            if s.check() == sat:
                model = s.model()
                schedule = []
                for i in range(n):
                    friend_idx = model[order[i]].as_long()
                    start_minutes = model[start_times[i]].as_long()
                    end_minutes = start_minutes + durations[friend_idx]
                    start_time = (base_time + timedelta(minutes=start_minutes)).strftime('%H:%M')
                    end_time = (base_time + timedelta(minutes=end_minutes)).strftime('%H:%M')
                    schedule.append({
                        "action": "meet",
                        "person": friends[friend_idx],
                        "start_time": start_time,
                        "end_time": end_time
                    })
                result_schedule = schedule
                solution_found = True
                break
        if solution_found:
            break
    
    # Output the result
    print('SOLUTION:')
    print(f'{{"itinerary": {result_schedule}}}')

if __name__ == "__main__":
    main()