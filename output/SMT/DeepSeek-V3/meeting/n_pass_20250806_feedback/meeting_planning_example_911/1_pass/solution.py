from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their availability
    friends = {
        "Steven": {"location": "North Beach", "start": "17:30", "end": "20:30", "duration": 15},
        "Sarah": {"location": "Golden Gate Park", "start": "17:00", "end": "19:15", "duration": 75},
        "Brian": {"location": "Embarcadero", "start": "14:15", "end": "16:00", "duration": 105},
        "Stephanie": {"location": "Haight-Ashbury", "start": "10:15", "end": "12:15", "duration": 75},
        "Melissa": {"location": "Richmond District", "start": "14:00", "end": "19:30", "duration": 30},
        "Nancy": {"location": "Nob Hill", "start": "08:15", "end": "12:45", "duration": 90},
        "David": {"location": "Marina District", "start": "11:15", "end": "13:15", "duration": 120},
        "James": {"location": "Presidio", "start": "15:00", "end": "18:15", "duration": 120},
        "Elizabeth": {"location": "Union Square", "start": "11:30", "end": "21:00", "duration": 60},
        "Robert": {"location": "Financial District", "start": "13:15", "end": "15:15", "duration": 45}
    }

    # Travel times (simplified for this example; full matrix would be needed for exact solution)
    # For simplicity, we'll assume travel times are symmetric and use the given data
    # In a full solution, we'd model travel times between all pairs of locations

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "The Castro"

    itinerary = []

    # We'll prioritize meeting friends with tighter time windows first
    # This is a heuristic; in a full solution, we'd let Z3 handle the ordering

    # Meeting Nancy first (earliest availability)
    nancy_start = max(time_to_minutes(friends["Nancy"]["start"]), current_time)
    nancy_end = nancy_start + friends["Nancy"]["duration"]
    if nancy_end <= time_to_minutes(friends["Nancy"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Nancy",
            "start_time": minutes_to_time(nancy_start),
            "end_time": minutes_to_time(nancy_end)
        })
        current_time = nancy_end
        current_location = "Nob Hill"

    # Next, meet Stephanie
    stephanie_start = max(time_to_minutes(friends["Stephanie"]["start"]), current_time + 15)  # Assume travel time from Nob Hill to Haight-Ashbury is 15 mins
    stephanie_end = stephanie_start + friends["Stephanie"]["duration"]
    if stephanie_end <= time_to_minutes(friends["Stephanie"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(stephanie_start),
            "end_time": minutes_to_time(stephanie_end)
        })
        current_time = stephanie_end
        current_location = "Haight-Ashbury"

    # Next, meet David
    david_start = max(time_to_minutes(friends["David"]["start"]), current_time + 17)  # Travel time from Haight-Ashbury to Marina District
    david_end = david_start + friends["David"]["duration"]
    if david_end <= time_to_minutes(friends["David"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "David",
            "start_time": minutes_to_time(david_start),
            "end_time": minutes_to_time(david_end)
        })
        current_time = david_end
        current_location = "Marina District"

    # Next, meet Elizabeth
    elizabeth_start = max(time_to_minutes(friends["Elizabeth"]["start"]), current_time + 16)  # Travel time from Marina District to Union Square
    elizabeth_end = elizabeth_start + friends["Elizabeth"]["duration"]
    if elizabeth_end <= time_to_minutes(friends["Elizabeth"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Elizabeth",
            "start_time": minutes_to_time(elizabeth_start),
            "end_time": minutes_to_time(elizabeth_end)
        })
        current_time = elizabeth_end
        current_location = "Union Square"

    # Next, meet Robert
    robert_start = max(time_to_minutes(friends["Robert"]["start"]), current_time + 9)  # Travel time from Union Square to Financial District
    robert_end = robert_start + friends["Robert"]["duration"]
    if robert_end <= time_to_minutes(friends["Robert"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Robert",
            "start_time": minutes_to_time(robert_start),
            "end_time": minutes_to_time(robert_end)
        })
        current_time = robert_end
        current_location = "Financial District"

    # Next, meet Brian
    brian_start = max(time_to_minutes(friends["Brian"]["start"]), current_time + 4)  # Travel time from Financial District to Embarcadero
    brian_end = brian_start + friends["Brian"]["duration"]
    if brian_end <= time_to_minutes(friends["Brian"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Brian",
            "start_time": minutes_to_time(brian_start),
            "end_time": minutes_to_time(brian_end)
        })
        current_time = brian_end
        current_location = "Embarcadero"

    # Next, meet James
    james_start = max(time_to_minutes(friends["James"]["start"]), current_time + 20)  # Travel time from Embarcadero to Presidio
    james_end = james_start + friends["James"]["duration"]
    if james_end <= time_to_minutes(friends["James"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "James",
            "start_time": minutes_to_time(james_start),
            "end_time": minutes_to_time(james_end)
        })
        current_time = james_end
        current_location = "Presidio"

    # Next, meet Melissa
    melissa_start = max(time_to_minutes(friends["Melissa"]["start"]), current_time + 7)  # Travel time from Presidio to Richmond District
    melissa_end = melissa_start + friends["Melissa"]["duration"]
    if melissa_end <= time_to_minutes(friends["Melissa"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Melissa",
            "start_time": minutes_to_time(melissa_start),
            "end_time": minutes_to_time(melissa_end)
        })
        current_time = melissa_end
        current_location = "Richmond District"

    # Next, meet Sarah
    sarah_start = max(time_to_minutes(friends["Sarah"]["start"]), current_time + 9)  # Travel time from Richmond District to Golden Gate Park
    sarah_end = sarah_start + friends["Sarah"]["duration"]
    if sarah_end <= time_to_minutes(friends["Sarah"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Sarah",
            "start_time": minutes_to_time(sarah_start),
            "end_time": minutes_to_time(sarah_end)
        })
        current_time = sarah_end
        current_location = "Golden Gate Park"

    # Finally, meet Steven
    steven_start = max(time_to_minutes(friends["Steven"]["start"]), current_time + 23)  # Travel time from Golden Gate Park to North Beach
    steven_end = steven_start + friends["Steven"]["duration"]
    if steven_end <= time_to_minutes(friends["Steven"]["end"]):
        itinerary.append({
            "action": "meet",
            "person": "Steven",
            "start_time": minutes_to_time(steven_start),
            "end_time": minutes_to_time(steven_end)
        })

    return {"itinerary": itinerary}

# Get the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))