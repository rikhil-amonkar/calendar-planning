from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Kimberly": {"location": "Presidio", "available_start": "15:30", "available_end": "16:00", "min_duration": 15},
        "Elizabeth": {"location": "Alamo Square", "available_start": "19:15", "available_end": "20:15", "min_duration": 15},
        "Joshua": {"location": "Marina District", "available_start": "10:30", "available_end": "14:15", "min_duration": 45},
        "Sandra": {"location": "Financial District", "available_start": "19:30", "available_end": "20:15", "min_duration": 45},
        "Kenneth": {"location": "Nob Hill", "available_start": "12:45", "available_end": "21:45", "min_duration": 30},
        "Betty": {"location": "Sunset District", "available_start": "14:00", "available_end": "19:00", "min_duration": 60},
        "Deborah": {"location": "Chinatown", "available_start": "17:15", "available_end": "20:30", "min_duration": 15},
        "Barbara": {"location": "Russian Hill", "available_start": "17:30", "available_end": "21:15", "min_duration": 120},
        "Steven": {"location": "North Beach", "available_start": "17:45", "available_end": "20:45", "min_duration": 90},
        "Daniel": {"location": "Haight-Ashbury", "available_start": "18:30", "available_end": "18:45", "min_duration": 15}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to make 9:00 AM as 0

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19
    }

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        start_var = Int(f"start_{friend}")
        end_var = Int(f"end_{friend}")
        meeting_vars[friend] = {
            "start": start_var,
            "end": end_var,
            "location": friends[friend]["location"],
            "available_start": time_to_minutes(friends[friend]["available_start"]),
            "available_end": time_to_minutes(friends[friend]["available_end"]),
            "min_duration": friends[friend]["min_duration"]
        }

    # Add basic constraints for each meeting
    for friend in friends:
        info = meeting_vars[friend]
        s.add(info["start"] >= info["available_start"])
        s.add(info["end"] <= info["available_end"])
        s.add(info["end"] - info["start"] >= info["min_duration"])

    # Create variables to represent the order of meetings
    meeting_order = [Int(f"order_{friend}") for friend in friends]
    s.add(Distinct(meeting_order))
    for i in range(len(meeting_order)):
        s.add(meeting_order[i] >= 0)
        s.add(meeting_order[i] < len(friends))

    # Add travel time constraints between all pairs of meetings
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(len(friend_list)):
            if i != j:
                # If meeting i comes before meeting j
                i_before_j = meeting_order[i] < meeting_order[j]
                # Then meeting j must start after meeting i ends plus travel time
                travel_time = travel_times.get(
                    (meeting_vars[friend_list[i]]["location"],
                    meeting_vars[friend_list[j]]["location"]),
                    0
                )
                s.add(Implies(
                    i_before_j,
                    meeting_vars[friend_list[j]]["start"] >= 
                    meeting_vars[friend_list[i]]["end"] + travel_time
                ))

    # Special handling for Daniel's very short window
    # Ensure Daniel's meeting doesn't conflict with others
    daniel_start = meeting_vars["Daniel"]["start"]
    daniel_end = meeting_vars["Daniel"]["end"]
    for friend in friends:
        if friend != "Daniel":
            other_start = meeting_vars[friend]["start"]
            other_end = meeting_vars[friend]["end"]
            # Either Daniel is before or after this meeting
            s.add(Or(
                daniel_end + travel_times.get(
                    (meeting_vars["Daniel"]["location"],
                     meeting_vars[friend]["location"]), 0) <= other_start,
                other_end + travel_times.get(
                    (meeting_vars[friend]["location"],
                     meeting_vars["Daniel"]["location"]), 0) <= daniel_start
            ))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start_time = model[meeting_vars[friend]["start"]].as_long()
            end_time = model[meeting_vars[friend]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing some constraints
        # First, try removing Daniel's meeting
        temp_friends = friends.copy()
        del temp_friends["Daniel"]
        meeting_vars_temp = meeting_vars.copy()
        del meeting_vars_temp["Daniel"]
        
        # Create a temporary solver
        temp_s = Solver()
        for friend in temp_friends:
            info = meeting_vars_temp[friend]
            temp_s.add(info["start"] >= info["available_start"])
            temp_s.add(info["end"] <= info["available_end"])
            temp_s.add(info["end"] - info["start"] >= info["min_duration"])
        
        # Recreate order variables
        temp_order = [Int(f"order_{friend}") for friend in temp_friends]
        temp_s.add(Distinct(temp_order))
        for i in range(len(temp_order)):
            temp_s.add(temp_order[i] >= 0)
            temp_s.add(temp_order[i] < len(temp_friends))
        
        # Add travel constraints
        temp_friend_list = list(temp_friends.keys())
        for i in range(len(temp_friend_list)):
            for j in range(len(temp_friend_list)):
                if i != j:
                    i_before_j = temp_order[i] < temp_order[j]
                    travel_time = travel_times.get(
                        (meeting_vars_temp[temp_friend_list[i]]["location"],
                         meeting_vars_temp[temp_friend_list[j]]["location"]),
                        0
                    )
                    temp_s.add(Implies(
                        i_before_j,
                        meeting_vars_temp[temp_friend_list[j]]["start"] >= 
                        meeting_vars_temp[temp_friend_list[i]]["end"] + travel_time
                    ))
        
        if temp_s.check() == sat:
            model = temp_s.model()
            itinerary = []
            for friend in temp_friends:
                start_time = model[meeting_vars_temp[friend]["start"]].as_long()
                end_time = model[meeting_vars_temp[friend]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
            itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))