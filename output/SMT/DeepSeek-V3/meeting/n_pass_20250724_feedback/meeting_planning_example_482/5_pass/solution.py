from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Locations and their time windows
    locations = {
        'Haight-Ashbury': {'arrival': '09:00'},
        'Mission District': {'Stephanie': ('08:15', '13:45')},
        'Bayview': {'Sandra': ('13:00', '19:30')},
        'Pacific Heights': {'Richard': ('07:15', '10:15')},
        'Russian Hill': {'Brian': ('12:15', '16:00')},
        'Fisherman\'s Wharf': {'Jason': ('08:30', '17:45')}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7
    }

    # Minimum meeting durations (in minutes)
    min_durations = {
        'Stephanie': 90,
        'Sandra': 15,
        'Richard': 75,
        'Brian': 120,
        'Jason': 60
    }

    # Convert time strings to minutes since 00:00
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each meeting
    meetings = {}
    for person in min_durations:
        start_var = Int(f'start_{person}')
        end_var = Int(f'end_{person}')
        meetings[person] = (start_var, end_var)

    # Find location for each person
    person_locations = {}
    for loc in locations:
        for person in locations[loc]:
            if person != 'arrival':
                person_locations[person] = loc

    # Basic constraints for each meeting
    for person, (start, end) in meetings.items():
        loc = person_locations[person]
        window_start, window_end = locations[loc][person]
        window_start_min = time_to_minutes(window_start)
        window_end_min = time_to_minutes(window_end)
        
        s.add(start >= window_start_min)
        s.add(end <= window_end_min)
        s.add(end - start >= min_durations[person])

    # Starting point constraint - must start at Haight-Ashbury at 9:00 AM
    arrival_time = time_to_minutes('09:00')
    current_time = arrival_time
    current_location = 'Haight-Ashbury'

    # Try different meeting orders
    meeting_orders = [
        ['Stephanie', 'Richard', 'Brian', 'Sandra', 'Jason'],
        ['Richard', 'Stephanie', 'Brian', 'Sandra', 'Jason'],
        ['Stephanie', 'Brian', 'Richard', 'Sandra', 'Jason'],
        ['Jason', 'Brian', 'Stephanie', 'Sandra', 'Richard']
    ]

    solution_found = False
    result = {"error": "No feasible schedule found"}

    for order in meeting_orders:
        if solution_found:
            break
            
        temp_solver = Solver()
        temp_solver.add(s.assertions())
        
        # Reset current time and location for this order attempt
        current_time = arrival_time
        current_location = 'Haight-Ashbury'
        
        # Add sequencing constraints for this order
        for person in order:
            start, end = meetings[person]
            loc = person_locations[person]
            
            # Travel time from current location
            travel_time = travel_times[(current_location, loc)]
            temp_solver.add(start >= current_time + travel_time)
            
            # Update current time and location
            current_time = end
            current_location = loc
        
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            valid = True
            
            # Verify all constraints are satisfied
            current_time = arrival_time
            current_location = 'Haight-Ashbury'
            
            for person in order:
                start, end = meetings[person]
                start_time = model.eval(start).as_long()
                end_time = model.eval(end).as_long()
                
                # Check travel time
                loc = person_locations[person]
                travel_time = travel_times[(current_location, loc)]
                if start_time < current_time + travel_time:
                    valid = False
                    break
                
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_time = end_time
                current_location = loc
            
            if valid:
                result = {"itinerary": itinerary}
                solution_found = True

    return result

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))