from z3 import *
import json

def main():
    # Define meetings and their details
    meetings = ['Rebecca', 'Stephanie', 'Karen', 'Brian', 'Steven']
    locations = {
        'Rebecca': "Fisherman's Wharf",
        'Stephanie': 'Golden Gate Park',
        'Karen': 'Chinatown',
        'Brian': 'Union Square',
        'Steven': 'North Beach'
    }
    
    # Available start and end times in minutes from 9:00 AM
    available_start = {
        'Rebecca': 10,    # 9:10 AM
        'Stephanie': 120,  # 11:00 AM
        'Karen': 285,      # 1:45 PM (13:45)
        'Brian': 360,      # 3:00 PM (15:00)
        'Steven': 330      # 2:30 PM (14:30)
    }
    
    available_end = {
        'Rebecca': 135,    # 11:15 AM
        'Stephanie': 360,  # 3:00 PM (15:00)
        'Karen': 450,      # 4:30 PM (16:30)
        'Brian': 495,      # 5:15 PM (17:15)
        'Steven': 705      # 8:45 PM (20:45)
    }
    
    min_duration = {
        'Rebecca': 30,
        'Stephanie': 105,
        'Karen': 15,
        'Brian': 30,
        'Steven': 120
    }
    
    # Travel times between locations (in minutes)
    travel_dict = {
        'Financial District': {
            "Fisherman's Wharf": 10,
            'Golden Gate Park': 23,
            'Chinatown': 5,
            'Union Square': 9,
            'North Beach': 7
        },
        "Fisherman's Wharf": {
            'Golden Gate Park': 25,
            'Chinatown': 12,
            'Union Square': 13,
            'North Beach': 6,
            'Financial District': 11
        },
        'Golden Gate Park': {
            "Fisherman's Wharf": 24,
            'Chinatown': 23,
            'Union Square': 22,
            'North Beach': 24,
            'Financial District': 26
        },
        'Chinatown': {
            "Fisherman's Wharf": 8,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'North Beach': 3,
            'Financial District': 5
        },
        'Union Square': {
            "Fisherman's Wharf": 15,
            'Golden Gate Park': 22,
            'Chinatown': 7,
            'North Beach': 10,
            'Financial District': 9
        },
        'North Beach': {
            "Fisherman's Wharf": 5,
            'Golden Gate Park': 22,
            'Chinatown': 6,
            'Union Square': 7,
            'Financial District': 8
        }
    }
    
    # Create Z3 solver
    s_solver = Solver()
    
    # Create variables for start and end times for each meeting
    s_times = [Int(f's_{name}') for name in meetings]
    e_times = [Int(f'e_{name}') for name in meetings]
    
    # Create order variables (positions in the sequence)
    order = [Int(f'o{i}') for i in range(5)]
    
    # Constraints for order: distinct and within [0,4]
    s_solver.add(Distinct(order))
    for i in range(5):
        s_solver.add(order[i] >= 0, order[i] < 5)
    
    # Constraints for each meeting: start time, end time, and duration
    for i, name in enumerate(meetings):
        s_solver.add(s_times[i] >= available_start[name])
        s_solver.add(e_times[i] <= available_end[name])
        s_solver.add(e_times[i] - s_times[i] >= min_duration[name])
    
    # Constraint for the first meeting: must account for travel from Financial District
    for j in range(5):
        meeting_name = meetings[j]
        loc = locations[meeting_name]
        travel_time = travel_dict['Financial District'][loc]
        s_solver.add(Implies(order[0] == j, s_times[j] >= travel_time))
    
    # Constraints for consecutive meetings: travel time between locations
    for k in range(4):  # k from 0 to 3 (for consecutive pairs)
        for i in range(5):
            for j in range(5):
                if i == j:
                    continue
                loc_i = locations[meetings[i]]
                loc_j = locations[meetings[j]]
                travel_time = travel_dict[loc_i][loc_j]
                s_solver.add(Implies(And(order[k] == i, order[k+1] == j),
                              s_times[j] >= e_times[i] + travel_time))
    
    # Check for a solution
    if s_solver.check() == sat:
        model = s_solver.model()
        # Extract start and end times
        schedule = []
        for i, name in enumerate(meetings):
            s_val = model.eval(s_times[i]).as_long()
            e_val = model.eval(e_times[i]).as_long()
            # Convert minutes from 9:00 to time string
            start_hour = 9 + s_val // 60
            start_minute = s_val % 60
            end_hour = 9 + e_val // 60
            end_minute = e_val % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        # Sort by start time
        schedule.sort(key=lambda x: x['start_time'])
        # Output as JSON
        result = {"itinerary": schedule}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No feasible schedule found")

if __name__ == '__main__':
    main()