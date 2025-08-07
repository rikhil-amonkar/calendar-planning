from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        "Ronald": {
            "location": "Nob Hill",
            "available_start": (10, 0),  # 10:00 AM
            "available_end": (17, 0),    # 5:00 PM
            "min_duration": 105,          # minutes
        },
        "Sarah": {
            "location": "Russian Hill",
            "available_start": (7, 15),   # 7:15 AM
            "available_end": (9, 30),     # 9:30 AM
            "min_duration": 45,
        },
        "Helen": {
            "location": "The Castro",
            "available_start": (13, 30),  # 1:30 PM
            "available_end": (17, 0),     # 5:00 PM
            "min_duration": 120,
        },
        "Joshua": {
            "location": "Sunset District",
            "available_start": (14, 15), # 2:15 PM
            "available_end": (19, 30),    # 7:30 PM
            "min_duration": 90,
        },
        "Margaret": {
            "location": "Haight-Ashbury",
            "available_start": (10, 15), # 10:15 AM
            "available_end": (22, 0),     # 10:00 PM
            "min_duration": 60,
        }
    }

    # Current location is Pacific Heights at 9:00 AM
    current_time = (9, 0)  # 9:00 AM
    current_location = "Pacific Heights"

    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        "Pacific Heights": {
            "Nob Hill": 8,
            "Russian Hill": 7,
            "The Castro": 16,
            "Sunset District": 21,
            "Haight-Ashbury": 11,
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Russian Hill": 5,
            "The Castro": 17,
            "Sunset District": 25,
            "Haight-Ashbury": 13,
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Nob Hill": 5,
            "The Castro": 21,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Russian Hill": 18,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
        },
        "Sunset District": {
            "Pacific Heights": 21,
            "Nob Hill": 27,
            "Russian Hill": 24,
            "The Castro": 17,
            "Haight-Ashbury": 15,
        },
        "Haight-Ashbury": {
            "Pacific Heights": 12,
            "Nob Hill": 15,
            "Russian Hill": 17,
            "The Castro": 6,
            "Sunset District": 15,
        }
    }

    # Convert all times to minutes since midnight for easier arithmetic
    def time_to_minutes(h, m):
        return h * 60 + m

    # Convert minutes back to (h, m)
    def minutes_to_time(total_minutes):
        h = total_minutes // 60
        m = total_minutes % 60
        return (h, m)

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end, 'location': friends[name]['location']}

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start_var = meeting_vars[name]['start']
        end_var = meeting_vars[name]['end']
        available_start = time_to_minutes(*friend['available_start'])
        available_end = time_to_minutes(*friend['available_end'])
        min_duration = friend['min_duration']

        # Meeting must start within availability window
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        # Meeting duration must be at least min_duration
        s.add(end_var - start_var >= min_duration)
        # Start must be before end
        s.add(start_var < end_var)

    # Define the order of meetings as a list to explore different sequences
    meeting_order = list(friends.keys())

    # Constraints for travel times between meetings
    for i in range(len(meeting_order) - 1):
        current_meeting = meeting_order[i]
        next_meeting = meeting_order[i + 1]
        current_location = meeting_vars[current_meeting]['location']
        next_location = meeting_vars[next_meeting]['location']
        travel_time = travel_times[current_location][next_location]
        s.add(meeting_vars[next_meeting]['start'] >= meeting_vars[current_meeting]['end'] + travel_time)

    # Initial travel from Pacific Heights to the first meeting
    first_meeting = meeting_order[0]
    first_location = meeting_vars[first_meeting]['location']
    initial_travel_time = travel_times[current_location][first_location]
    s.add(meeting_vars[first_meeting]['start'] >= time_to_minutes(*current_time) + initial_travel_time)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect all meetings with their times
        meetings = []
        for name in friends:
            start_val = model[meeting_vars[name]['start']].as_long()
            end_val = model[meeting_vars[name]['end']].as_long()
            start_time = minutes_to_time(start_val)
            end_time = minutes_to_time(end_val)
            meetings.append({
                'name': name,
                'start': start_time,
                'end': end_time
            })

        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])

        # Format itinerary
        for meeting in meetings:
            name = meeting['name']
            start_h, start_m = meeting['start']
            end_h, end_m = meeting['end']
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })

        return {"itinerary": itinerary}
    else:
        # If no solution found, try a different order
        # Here, we try a specific order that might work
        meeting_order = ["Sarah", "Ronald", "Margaret", "Helen", "Joshua"]
        s.reset()
        
        # Re-add all constraints with the new order
        for name in friends:
            friend = friends[name]
            start_var = meeting_vars[name]['start']
            end_var = meeting_vars[name]['end']
            available_start = time_to_minutes(*friend['available_start'])
            available_end = time_to_minutes(*friend['available_end'])
            min_duration = friend['min_duration']

            s.add(start_var >= available_start)
            s.add(end_var <= available_end)
            s.add(end_var - start_var >= min_duration)
            s.add(start_var < end_var)

        for i in range(len(meeting_order) - 1):
            current_meeting = meeting_order[i]
            next_meeting = meeting_order[i + 1]
            current_location = meeting_vars[current_meeting]['location']
            next_location = meeting_vars[next_meeting]['location']
            travel_time = travel_times[current_location][next_location]
            s.add(meeting_vars[next_meeting]['start'] >= meeting_vars[current_meeting]['end'] + travel_time)

        first_meeting = meeting_order[0]
        first_location = meeting_vars[first_meeting]['location']
        initial_travel_time = travel_times[current_location][first_location]
        s.add(meeting_vars[first_meeting]['start'] >= time_to_minutes(*current_time) + initial_travel_time)

        if s.check() == sat:
            model = s.model()
            itinerary = []

            meetings = []
            for name in friends:
                start_val = model[meeting_vars[name]['start']].as_long()
                end_val = model[meeting_vars[name]['end']].as_long()
                start_time = minutes_to_time(start_val)
                end_time = minutes_to_time(end_val)
                meetings.append({
                    'name': name,
                    'start': start_time,
                    'end': end_time
                })

            meetings.sort(key=lambda x: x['start'])

            for meeting in meetings:
                name = meeting['name']
                start_h, start_m = meeting['start']
                end_h, end_m = meeting['end']
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })

            return {"itinerary": itinerary}
        else:
            return {"error": "No feasible schedule found with the given constraints."}

# Execute the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))