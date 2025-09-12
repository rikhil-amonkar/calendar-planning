from z3 import *
import json

def main():
    # Convert all times to minutes since 9:00 AM (which is 0 minutes)
    travel_times = {
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Bayview'): 22,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Fisherman\'s Wharf'): 25
    }
    
    # Friend constraints: (name, location, available_start, available_end, min_duration)
    friends = [
        ('Helen', 'North Beach', 0, 465, 120),   # available from 9:00 AM (0) to 4:45 PM (465)
        ('Kimberly', 'Fisherman\'s Wharf', 450, 720, 45),  # available from 4:30 PM (450) to 9:00 PM (720)
        ('Patricia', 'Bayview', 540, 735, 120)   # available from 6:00 PM (540) to 9:15 PM (735)
    ]
    
    # Initialize Z3 variables for each friend
    variables = {}
    for name, loc, avail_start, avail_end, min_dur in friends:
        variables[name] = {
            'start': Int(f'{name}_start'),
            'end': Int(f'{name}_end'),
            'occur': Bool(f'{name}_occur'),
            'arrival': Int(f'{name}_arrival'),
            'loc': loc,
            'avail_start': avail_start,
            'avail_end': avail_end,
            'min_dur': min_dur
        }
    
    s = Optimize()
    
    # Constraints for each friend
    for name, data in variables.items():
        # If meeting occurs, enforce time constraints and duration
        s.add(Implies(data['occur'], data['start'] >= data['avail_start']))
        s.add(Implies(data['occur'], data['end'] <= data['avail_end']))
        s.add(Implies(data['occur'], data['end'] == data['start'] + data['min_dur']))
        
        # Arrival time must account for travel from Nob Hill
        travel_from_nob = travel_times[('Nob Hill', data['loc'])]
        s.add(Implies(data['occur'], data['arrival'] >= travel_from_nob))
        s.add(Implies(data['occur'], data['start'] >= data['arrival']))
    
    # Constraints for travel between meetings
    friend_names = list(variables.keys())
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            name_i = friend_names[i]
            name_j = friend_names[j]
            data_i = variables[name_i]
            data_j = variables[name_j]
            
            both_occur = And(data_i['occur'], data_j['occur'])
            travel_ij = travel_times[(data_i['loc'], data_j['loc'])]
            travel_ji = travel_times[(data_j['loc'], data_i['loc'])]
            
            # Ensure enough travel time between meetings
            constraint = Or(
                data_j['arrival'] >= data_i['end'] + travel_ij,
                data_i['arrival'] >= data_j['end'] + travel_ji
            )
            s.add(Implies(both_occur, constraint))
    
    # Maximize number of meetings
    meeting_occurrences = [If(variables[name]['occur'], 1, 0) for name in variables]
    s.maximize(Sum(meeting_occurrences))
    
    # Convert minutes to time string (e.g., 60 -> "10:00")
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, data in variables.items():
            if is_true(model.evaluate(data['occur'])):
                start_val = model.evaluate(data['start']).as_long()
                end_val = model.evaluate(data['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": data['loc'],
                    "person": name,
                    "start_time": format_time(start_val),
                    "end_time": format_time(end_val)
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()