from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Financial District'): 5,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Financial District'): 19,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Financial District'): 23,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Presidio'): 22,
    }

    # Define friends' availability and meeting duration requirements
    friends = [
        {
            'name': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': (8, 45),  # 8:45 AM
            'available_end': (11, 45),  # 11:45 AM
            'duration': 45,  # minutes
        },
        {
            'name': 'Kevin',
            'location': 'Haight-Ashbury',
            'available_start': (10, 15),  # 10:15 AM
            'available_end': (16, 15),  # 4:15 PM
            'duration': 90,  # minutes
        },
        {
            'name': 'Deborah',
            'location': 'Bayview',
            'available_start': (15, 0),  # 3:00 PM
            'available_end': (19, 15),  # 7:15 PM
            'duration': 120,  # minutes
        },
        {
            'name': 'Stephanie',
            'location': 'Presidio',
            'available_start': (10, 0),  # 10:00 AM
            'available_end': (17, 15),  # 5:15 PM
            'duration': 120,  # minutes
        },
        {
            'name': 'Emily',
            'location': 'Financial District',
            'available_start': (11, 30),  # 11:30 AM
            'available_end': (21, 45),  # 9:45 PM
            'duration': 105,  # minutes
        }
    ]

    # Convert time to minutes since midnight
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to HH:MM format
    def minutes_to_time(total_minutes):
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    # Define variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        s.add(start >= time_to_minutes(*friend['available_start']))
        s.add(end <= time_to_minutes(*friend['available_end']))
        s.add(end == start + friend['duration'])
        meeting_vars.append((friend['name'], start, end, friend['location']))

    # Define the order of meetings to reduce complexity
    # Here we choose an order that seems feasible based on locations and times
    order = ['Mary', 'Kevin', 'Stephanie', 'Emily', 'Deborah']

    # Ensure the first meeting starts after arrival at Embarcadero (9:00 AM) plus travel time
    first_meeting_name = order[0]
    first_meeting_loc = next(f['location'] for f in friends if f['name'] == first_meeting_name)
    travel_time = travel_times[('Embarcadero', first_meeting_loc)]
    first_meeting_start = next(s for (n, s, e, l) in meeting_vars if n == first_meeting_name)
    s.add(first_meeting_start >= time_to_minutes(9, 0) + travel_time)

    # Add constraints for travel times between meetings
    for i in range(len(order) - 1):
        current_person = order[i]
        next_person = order[i + 1]
        current_loc = next(f['location'] for f in friends if f['name'] == current_person)
        next_loc = next(f['location'] for f in friends if f['name'] == next_person)
        travel_time = travel_times[(current_loc, next_loc)]
        current_end = next(e for (n, s, e, l) in meeting_vars if n == current_person)
        next_start = next(s for (n, s, e, l) in meeting_vars if n == next_person)
        s.add(next_start >= current_end + travel_time)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, start_var, end_var, _ in meeting_vars:
            start_time = model.evaluate(start_var).as_long()
            end_time = model.evaluate(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))