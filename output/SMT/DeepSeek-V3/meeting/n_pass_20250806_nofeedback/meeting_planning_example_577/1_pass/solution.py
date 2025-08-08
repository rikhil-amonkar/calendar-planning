from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {
            "name": "Stephanie",
            "location": "Russian Hill",
            "available_start": "20:00",
            "available_end": "20:45",
            "min_duration": 15
        },
        {
            "name": "Kevin",
            "location": "Fisherman's Wharf",
            "available_start": "19:15",
            "available_end": "21:45",
            "min_duration": 75
        },
        {
            "name": "Robert",
            "location": "Nob Hill",
            "available_start": "07:45",
            "available_end": "10:30",
            "min_duration": 90
        },
        {
            "name": "Steven",
            "location": "Golden Gate Park",
            "available_start": "08:30",
            "available_end": "17:00",
            "min_duration": 75
        },
        {
            "name": "Anthony",
            "location": "Alamo Square",
            "available_start": "07:45",
            "available_end": "19:45",
            "min_duration": 15
        },
        {
            "name": "Sandra",
            "location": "Pacific Heights",
            "available_start": "14:45",
            "available_end": "21:45",
            "min_duration": 45
        }
    ]

    # Convert time strings to minutes since midnight for easier handling
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location is Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = time_to_minutes("09:00")
    current_location = "Haight-Ashbury"

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Haight-Ashbury": {
            "Russian Hill": 17,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Alamo Square": 5,
            "Pacific Heights": 12
        },
        "Russian Hill": {
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "Nob Hill": 5,
            "Golden Gate Park": 21,
            "Alamo Square": 15,
            "Pacific Heights": 7
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Russian Hill": 7,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Alamo Square": 20,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Haight-Ashbury": 13,
            "Russian Hill": 5,
            "Fisherman's Wharf": 11,
            "Golden Gate Park": 17,
            "Alamo Square": 11,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Russian Hill": 19,
            "Fisherman's Wharf": 24,
            "Nob Hill": 20,
            "Alamo Square": 10,
            "Pacific Heights": 16
        },
        "Alamo Square": {
            "Haight-Ashbury": 5,
            "Russian Hill": 13,
            "Fisherman's Wharf": 19,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Haight-Ashbury": 11,
            "Russian Hill": 7,
            "Fisherman's Wharf": 13,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Alamo Square": 10
        }
    }

    # Create Z3 variables for each friend's meeting start and end times
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['min_duration']
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        meetings.append({
            "name": friend['name'],
            "location": friend['location'],
            "start": start,
            "end": end,
            "duration": duration,
            "available_start": available_start,
            "available_end": available_end
        })

    # Constraints for each meeting
    for meeting in meetings:
        s.add(meeting['start'] >= meeting['available_start'])
        s.add(meeting['end'] <= meeting['available_end'])
        s.add(meeting['end'] == meeting['start'] + meeting['duration'])

    # Order of meetings and travel times
    # We need to decide the order in which to meet friends. This is a complex part.
    # For simplicity, let's assume we can meet friends in any order, but we'll need to sequence them properly with travel times.
    # This is a simplified approach; a more comprehensive solution would involve permutations.

    # For this example, let's try a specific order that might work: Robert, Steven, Anthony, Sandra, Kevin, Stephanie
    # This is a heuristic; in a real scenario, we'd need to explore all possible permutations or use a more sophisticated approach.

    # Let's define the order as a list of indices in the 'meetings' list.
    # We'll try the order: Robert (index 2), Steven (3), Anthony (4), Sandra (5), Kevin (1), Stephanie (0)
    order = [2, 3, 4, 5, 1, 0]

    # Add constraints for travel times between consecutive meetings
    prev_location = current_location
    prev_end = current_time
    for i in order:
        meeting = meetings[i]
        travel_time = travel_times[prev_location][meeting['location']]
        s.add(meeting['start'] >= prev_end + travel_time)
        prev_location = meeting['location']
        prev_end = meeting['end']

    # Also, ensure that no two meetings overlap (though the order should prevent this)
    # This is redundant given the travel constraints, but added for safety
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            mi = meetings[i]
            mj = meetings[j]
            s.add(Or(mi['end'] <= mj['start'], mj['end'] <= mi['start']))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start_val = model[meeting['start']].as_long()
            end_val = model[meeting['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))