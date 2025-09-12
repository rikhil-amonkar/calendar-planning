from z3 import *
import json

def main():
    # Travel time matrix (in minutes)
    travel_time = {
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 24,
            'Bayview': 23,
            'Mission District': 17,
            'Embarcadero': 25,
            'Financial District': 26
        },
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Bayview': 26,
            'Mission District': 22,
            'Embarcadero': 8,
            'Financial District': 11
        },
        'Bayview': {
            'Golden Gate Park': 22,
            'Fisherman\'s Wharf': 25,
            'Mission District': 13,
            'Embarcadero': 19,
            'Financial District': 19
        },
        'Mission District': {
            'Golden Gate Park': 17,
            'Fisherman\'s Wharf': 22,
            'Bayview': 15,
            'Embarcadero': 19,
            'Financial District': 17
        },
        'Embarcadero': {
            'Golden Gate Park': 25,
            'Fisherman\'s Wharf': 6,
            'Bayview': 21,
            'Mission District': 20,
            'Financial District': 5
        },
        'Financial District': {
            'Golden Gate Park': 23,
            'Fisherman\'s Wharf': 10,
            'Bayview': 19,
            'Mission District': 17,
            'Embarcadero': 4
        }
    }
    
    # Convert all times to minutes since midnight
    start_time_golden_gate = 9 * 60  # 9:00 AM
    people = [
        {
            'name': 'Joseph',
            'location': 'Fisherman\'s Wharf',
            'avail_start': 8 * 60,      # 8:00 AM
            'avail_end': 17 * 60 + 30,  # 5:30 PM
            'min_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Bayview',
            'avail_start': 17 * 60 + 30, # 5:30 PM
            'avail_end': 21 * 60 + 30,   # 9:30 PM
            'min_duration': 60
        },
        {
            'name': 'Kevin',
            'location': 'Mission District',
            'avail_start': 11 * 60 + 15, # 11:15 AM
            'avail_end': 15 * 60 + 15,   # 3:15 PM
            'min_duration': 30
        },
        {
            'name': 'David',
            'location': 'Embarcadero',
            'avail_start': 8 * 60 + 15,  # 8:15 AM
            'avail_end': 9 * 60,         # 9:00 AM
            'min_duration': 30
        },
        {
            'name': 'Barbara',
            'location': 'Financial District',
            'avail_start': 10 * 60 + 30, # 10:30 AM
            'avail_end': 16 * 60 + 30,   # 4:30 PM
            'min_duration': 15
        }
    ]
    
    # Initialize Z3 solver and variables
    solver = Optimize()
    
    # Create variables for each person: whether we meet them, start time, and end time
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    
    for person in people:
        name = person['name']
        meet_vars[name] = Bool(f'meet_{name}')
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')
    
    # Current location and time
    current_location = 'Golden Gate Park'
    current_time = start_time_golden_gate
    
    # Constraints for each person
    for person in people:
        name = person['name']
        loc = person['location']
        avail_start = person['avail_start']
        avail_end = person['avail_end']
        min_dur = person['min_duration']
        
        # If we meet this person, constraints on time and duration
        solver.add(Implies(meet_vars[name], 
                          And(start_vars[name] >= avail_start,
                             end_vars[name] <= avail_end,
                             end_vars[name] - start_vars[name] >= min_dur)))
        
        # If we don't meet them, start and end are 0
        solver.add(Implies(Not(meet_vars[name]), 
                          And(start_vars[name] == 0, end_vars[name] == 0)))
    
    # Sequence constraints: ensure meetings don't overlap and account for travel
    # We need to define an order of meetings. We'll use a continuous timeline.
    # For any two meetings that both happen, one must come after the other with travel time.
    for i, person1 in enumerate(people):
        for j, person2 in enumerate(people):
            if i == j:
                continue
            name1 = person1['name']
            name2 = person2['name']
            loc1 = person1['location']
            loc2 = person2['location']
            travel = travel_time[loc1][loc2]
            
            # If both meetings happen, then either meeting1 ends before meeting2 starts minus travel,
            # or meeting2 ends before meeting1 starts minus travel.
            solver.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                              Or(end_vars[name1] + travel <= start_vars[name2],
                                 end_vars[name2] + travel <= start_vars[name1])))
    
    # Constraint: first meeting must account for travel from Golden Gate Park
    for person in people:
        name = person['name']
        loc = person['location']
        travel = travel_time[current_location][loc]
        solver.add(Implies(meet_vars[name], start_vars[name] >= current_time + travel))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet_vars[person['name']], 1, 0) for person in people])
    solver.maximize(total_meetings)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Collect all meetings that are scheduled
        meetings_scheduled = []
        for person in people:
            name = person['name']
            if is_true(model.eval(meet_vars[name])):
                start_val = model.eval(start_vars[name]).as_long()
                end_val = model.eval(end_vars[name]).as_long()
                meetings_scheduled.append({
                    'name': name,
                    'location': person['location'],
                    'start': start_val,
                    'end': end_val
                })
        
        # Sort meetings by start time
        meetings_scheduled.sort(key=lambda x: x['start'])
        
        # Convert to output format
        for meeting in meetings_scheduled:
            # Convert minutes to time string
            start_h = meeting['start'] // 60
            start_m = meeting['start'] % 60
            end_h = meeting['end'] // 60
            end_m = meeting['end'] % 60
            
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": f"{start_h}:{start_m:02d}",
                "end_time": f"{end_h}:{end_m:02d}"
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()