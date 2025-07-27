from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their respective time windows
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

    # Constraints for each meeting
    for person, (start, end) in meetings.items():
        # Find the location and time window for the person
        location = None
        window_start, window_end = None, None
        for loc in locations:
            if person in locations[loc]:
                location = loc
                window_start, window_end = locations[loc][person]
                break
        window_start_min = time_to_minutes(window_start)
        window_end_min = time_to_minutes(window_end)
        
        # Meeting must be within the person's availability
        s.add(start >= window_start_min)
        s.add(end <= window_end_min)
        
        # Meeting duration must be at least the minimum
        s.add(end - start >= min_durations[person])

    # Starting point: Haight-Ashbury at 09:00
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes('09:00')

    # Order of meetings to try (this can be adjusted for optimization)
    meeting_order = ['Richard', 'Stephanie', 'Brian', 'Sandra', 'Jason']

    # Track the order of meetings and travel times
    for person in meeting_order:
        start, end = meetings[person]
        
        # Find the person's location
        person_location = None
        for loc in locations:
            if person in locations[loc]:
                person_location = loc
                break
        
        # Travel to the person's location
        travel_time = travel_times.get((current_location, person_location), 0)
        s.add(start >= current_time + travel_time)
        
        # Update current location and time
        current_location = person_location
        current_time = end

    # Try to meet as many friends as possible
    # Here, we prioritize meeting all friends, but the constraints ensure feasibility
    if s.check() == sat:
        model = s.model()

        # Extract the meeting times from the model
        itinerary = []
        for person in meetings:
            start, end = meetings[person]
            start_time = model.eval(start).as_long()
            end_time = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })

        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))