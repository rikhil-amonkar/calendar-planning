from z3 import *
import json

def main():
    # Travel time matrix (7x7)
    # Index: 0=Embarcadero, 1=Richmond District, 2=Union Square, 3=Financial District, 4=Pacific Heights, 5=Nob Hill, 6=Bayview
    travel_matrix = [
        [0, 21, 10, 5, 11, 10, 21],
        [19, 0, 21, 22, 10, 17, 26],
        [11, 20, 0, 9, 15, 9, 15],
        [4, 21, 9, 0, 13, 8, 19],
        [10, 12, 12, 13, 0, 8, 22],
        [9, 14, 7, 9, 8, 0, 19],
        [19, 25, 17, 19, 23, 20, 0]
    ]
    
    # Friends data: (name, location_index, available_start, available_end, min_duration)
    friends = [
        ('Kenneth', 1, 735, 780, 30),   # Richmond District, 9:15PM-10:00PM
        ('Lisa', 2, 0, 450, 45),         # Union Square, 9:00AM-4:30PM
        ('Joshua', 3, 180, 375, 15),     # Financial District, 12:00PM-3:15PM
        ('Nancy', 4, 0, 150, 90),        # Pacific Heights, 9:00AM-11:30AM (adjusted from 8:00AM)
        ('Andrew', 5, 150, 675, 60),     # Nob Hill, 11:30AM-8:15PM
        ('John', 6, 465, 750, 75)        # Bayview, 4:45PM-9:30PM
    ]
    
    location_names = ['Embarcadero', 'Richmond District', 'Union Square', 'Financial District', 'Pacific Heights', 'Nob Hill', 'Bayview']
    
    n = len(friends)
    solver = Optimize()
    
    # Decision variables
    included = [Bool(f'included_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Constraints for each friend
    for i in range(n):
        name, loc_idx, avail_start, avail_end, min_dur = friends[i]
        # If meeting is included, enforce time window and duration
        solver.add(Implies(included[i], start[i] >= avail_start))
        solver.add(Implies(included[i], end[i] <= avail_end))
        solver.add(Implies(included[i], end[i] - start[i] >= min_dur))
        # Order must be between 0 and n-1 if included, else -1
        solver.add(Implies(included[i], And(order[i] >= 0, order[i] < n)))
        solver.add(Implies(Not(included[i]), order[i] == -1))
        # Start time must allow travel from Embarcadero
        solver.add(Implies(included[i], start[i] >= travel_matrix[0][loc_idx]))
    
    # All included meetings have distinct orders
    for i in range(n):
        for j in range(i+1, n):
            solver.add(Implies(And(included[i], included[j]), order[i] != order[j]))
    
    # Travel time constraints between meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            cond = And(included[i], included[j], order[i] < order[j])
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            travel_time = travel_matrix[loc_i][loc_j]
            solver.add(Implies(cond, end[i] + travel_time <= start[j]))
    
    # Maximize number of meetings
    objective = Sum([If(included[i], 1, 0) for i in range(n)])
    solver.maximize(objective)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        meetings = []
        for i in range(n):
            if model.evaluate(included[i]):
                order_val = model.evaluate(order[i]).as_long()
                start_val = model.evaluate(start[i]).as_long()
                end_val = model.evaluate(end[i]).as_long()
                name, loc_idx, _, _, _ = friends[i]
                location = location_names[loc_idx]
                meetings.append((order_val, name, location, start_val, end_val))
        
        meetings.sort(key=lambda x: x[0])
        for meeting in meetings:
            _, name, location, start_val, end_val = meeting
            # Convert minutes to time string (24-hour format)
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()