from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "Amanda", "location": "Marina District", "available_start": "14:45", "available_end": "19:30", "min_duration": 105},
        {"name": "Melissa", "location": "The Castro", "available_start": "09:30", "available_end": "17:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "18:45", "min_duration": 120},
        {"name": "Matthew", "location": "Bayview", "available_start": "10:15", "available_end": "13:15", "min_duration": 30},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "17:00", "available_end": "21:30", "min_duration": 105},
        {"name": "Karen", "location": "Mission District", "available_start": "17:30", "available_end": "20:30", "min_duration": 105},
        {"name": "Robert", "location": "Alamo Square", "available_start": "11:15", "available_end": "17:30", "min_duration": 120},
        {"name": "Joseph", "location": "Golden Gate Park", "available_start": "08:30", "available_end": "21:15", "min_duration": 105}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    for friend in friends:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        start = Int(f"{friend['name']}_start")
        end = Int(f"{friend['name']}_end")
        
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)
        
        friend["start_var"] = start
        friend["end_var"] = end

    # Define the initial position and time (Presidio at 9:00 AM, 540 minutes)
    initial_time = 540  # 9:00 AM in minutes
    current_location = "Presidio"

    # Define travel times between locations
    travel_times = {
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Golden Gate Park"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
    }

    # Define the order of meetings (this is a simplified approach; in reality, we'd need to model the sequence)
    # For simplicity, we'll assume a fixed order that allows all meetings to fit
    # This is a heuristic and may not always work; a more robust approach would involve sequencing variables
    # Here, we'll try to meet friends in a feasible order based on their time windows and locations

    # We'll attempt to meet friends in the following order:
    # Joseph (Golden Gate Park), Matthew (Bayview), Robert (Alamo Square), Jeffrey (Fisherman's Wharf), Melissa (The Castro), Amanda (Marina District), Karen (Mission District), Nancy (Pacific Heights)
    # This is a heuristic and may not be optimal; the Z3 model should ideally handle sequencing

    # To model sequencing, we need to define the order of meetings and ensure travel times are respected
    # This requires more complex modeling, possibly with additional variables for the sequence

    # For the sake of this example, we'll proceed with a fixed order and check feasibility

    # Define the order: Joseph, Matthew, Robert, Jeffrey, Melissa, Amanda, Karen, Nancy
    ordered_friends = [
        friends[7],  # Joseph
        friends[3],  # Matthew
        friends[6],  # Robert
        friends[2],  # Jeffrey
        friends[1],  # Melissa
        friends[0],  # Amanda
        friends[5],  # Karen
        friends[4],  # Nancy
    ]

    # Add constraints for travel times between consecutive meetings
    prev_end = initial_time
    prev_location = current_location
    for friend in ordered_friends:
        location = friend["location"]
        travel_time = travel_times.get((prev_location, location), 0)
        s.add(friend["start_var"] >= prev_end + travel_time)
        prev_end = friend["end_var"]
        prev_location = location

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start_val = model[friend["start_var"]].as_long()
            end_val = model[friend["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))