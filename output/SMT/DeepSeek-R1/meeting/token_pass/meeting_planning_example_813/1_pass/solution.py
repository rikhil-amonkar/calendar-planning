import z3
import json

def main():
    # Travel time matrix (10x10)
    # Indices: 0:Marina District, 1:Embarcadero, 2:Bayview, 3:Union Square, 4:Chinatown,
    #          5:Sunset District, 6:Golden Gate Park, 7:Financial District, 8:Haight-Ashbury, 9:Mission District
    travel_time = [
        [0, 14, 27, 16, 15, 19, 18, 17, 16, 20],
        [12, 0, 21, 10, 7, 30, 25, 5, 21, 20],
        [27, 19, 0, 18, 19, 23, 22, 19, 19, 13],
        [18, 11, 15, 0, 7, 27, 22, 9, 18, 14],
        [12, 5, 20, 7, 0, 29, 23, 5, 19, 17],
        [21, 30, 22, 30, 30, 0, 11, 30, 15, 25],
        [16, 25, 23, 22, 23, 10, 0, 26, 7, 17],
        [15, 4, 19, 9, 5, 30, 23, 0, 19, 17],
        [17, 20, 18, 19, 19, 15, 7, 21, 0, 11],
        [19, 19, 14, 15, 16, 24, 17, 15, 12, 0]
    ]
    
    # Friends data: name, location index, available start (min from 9:00), available end (min from 9:00), duration
    friends = [
        {'name': 'Joshua', 'loc': 1, 'start': 45, 'end': 540, 'dur': 105},
        {'name': 'Jeffrey', 'loc': 2, 'start': 45, 'end': 675, 'dur': 75},
        {'name': 'Charles', 'loc': 3, 'start': 105, 'end': 675, 'dur': 120},
        {'name': 'Joseph', 'loc': 4, 'start': 15, 'end': 390, 'dur': 60},  # Adjusted start to 15 (9:00 + travel 15min)
        {'name': 'Elizabeth', 'loc': 5, 'start': 0, 'end': 45, 'dur': 45},
        {'name': 'Matthew', 'loc': 6, 'start': 120, 'end': 630, 'dur': 45},
        {'name': 'Carol', 'loc': 7, 'start': 105, 'end': 135, 'dur': 15},
        {'name': 'Paul', 'loc': 8, 'start': 615, 'end': 690, 'dur': 15},
        {'name': 'Rebecca', 'loc': 9, 'start': 480, 'end': 765, 'dur': 45}
    ]
    
    n = len(friends)
    solver = z3.Optimize()
    
    # Create variables for each friend
    meet_vars = []
    start_vars = []
    end_vars = []
    order_vars = []
    
    for i, friend in enumerate(friends):
        meet_vars.append(z3.Bool(f"meet_{i}"))
        start_vars.append(z3.Int(f"start_{i}"))
        end_vars.append(z3.Int(f"end_{i}"))
        order_vars.append(z3.Int(f"order_{i}"))
    
    # Constraints for each friend
    for i, friend in enumerate(friends):
        # If meeting, constraints on time and duration
        solver.add(z3.Implies(meet_vars[i], 
            z3.And(
                start_vars[i] >= friend['start'],
                end_vars[i] <= friend['end'],
                end_vars[i] - start_vars[i] >= friend['dur'],
                order_vars[i] >= 0,
                order_vars[i] < n
            )
        ))
        # If not meeting, order is -1
        solver.add(z3.Implies(z3.Not(meet_vars[i]), order_vars[i] == -1))
    
    # All met meetings have distinct orders
    for i in range(n):
        for j in range(i+1, n):
            solver.add(z3.Implies(z3.And(meet_vars[i], meet_vars[j]), order_vars[i] != order_vars[j]))
    
    # Constraints for travel times
    for i in range(n):
        # First meeting must account for travel from Marina District
        solver.add(z3.Implies(z3.And(meet_vars[i], order_vars[i] == 0), 
                   start_vars[i] >= travel_time[0][friends[i]['loc']]))
        # For subsequent meetings, travel from previous meeting
        for j in range(n):
            if i == j:
                continue
            solver.add(z3.Implies(
                z3.And(meet_vars[i], meet_vars[j], order_vars[j] == order_vars[i] - 1),
                start_vars[i] >= end_vars[j] + travel_time[friends[j]['loc']][friends[i]['loc']]
            ))
    
    # Maximize number of meetings
    meet_count = z3.Sum([z3.If(meet_vars[i], 1, 0) for i in range(n)])
    solver.maximize(meet_count)
    
    # Check feasibility
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        # Collect all meetings that are scheduled
        meetings = []
        for i, friend in enumerate(friends):
            if z3.is_true(model.eval(meet_vars[i])):
                order_val = model.eval(order_vars[i]).as_long()
                start_val = model.eval(start_vars[i]).as_long()
                end_val = model.eval(end_vars[i]).as_long()
                meetings.append({
                    'order': order_val,
                    'name': friend['name'],
                    'loc': friend['loc'],
                    'start': start_val,
                    'end': end_val
                })
        # Sort meetings by order
        meetings.sort(key=lambda x: x['order'])
        # Convert to itinerary format
        for meeting in meetings:
            # Convert minutes from 9:00 to time string
            start_minutes = 540 + meeting['start']  # 9:00 in minutes from midnight is 540
            end_minutes = 540 + meeting['end']
            start_hour = start_minutes // 60
            start_min = start_minutes % 60
            end_hour = end_minutes // 60
            end_min = end_minutes % 60
            start_str = f"{start_hour}:{start_min:02d}"
            end_str = f"{end_hour}:{end_min:02d}"
            
            # Map location index to name
            loc_names = [
                "Marina District", "Embarcadero", "Bayview", "Union Square", "Chinatown",
                "Sunset District", "Golden Gate Park", "Financial District", "Haight-Ashbury", "Mission District"
            ]
            loc_name = loc_names[meeting['loc']]
            
            itinerary.append({
                "action": "meet",
                "location": loc_name,
                "person": meeting['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()