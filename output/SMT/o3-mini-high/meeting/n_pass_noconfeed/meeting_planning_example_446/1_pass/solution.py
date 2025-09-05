from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()

    # Arrival information
    arrival_time = 9 * 60  # 9:00 in minutes
    arrival_location = "Richmond District"
    
    # Friend meeting constraints and details
    persons = ["Kimberly", "Robert", "Rebecca", "Margaret", "Kenneth"]
    details = {
        "Kimberly": {
            "location": "Marina District",
            "avail_start": 13 * 60 + 15,  # 13:15 -> 795
            "avail_end": 16 * 60 + 45,    # 16:45 -> 1005
            "min_duration": 15
        },
        "Robert": {
            "location": "Chinatown",
            "avail_start": 12 * 60 + 15,  # 12:15 -> 735
            "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
            "min_duration": 15
        },
        "Rebecca": {
            "location": "Financial District",
            "avail_start": 13 * 60 + 15,  # 13:15 -> 795
            "avail_end": 16 * 60 + 45,    # 16:45 -> 1005
            "min_duration": 75
        },
        "Margaret": {
            "location": "Bayview",
            "avail_start": 9 * 60 + 30,   # 9:30 -> 570
            "avail_end": 13 * 60 + 30,    # 13:30 -> 810
            "min_duration": 30
        },
        "Kenneth": {
            "location": "Union Square",
            "avail_start": 19 * 60 + 30,  # 19:30 -> 1170
            "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
            "min_duration": 75
        }
    }

    # Travel times (in minutes) as given in the problem
    travel = {
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Bayview"): 26,
        ("Richmond District", "Union Square"): 21,
        
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Chinatown"): 16,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Union Square"): 7,
        
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Union Square"): 17,
        
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Bayview"): 15
    }

    # Decision variables for each meeting of a friend:
    # start time, end time, and whether we choose to attend the meeting.
    meeting_vars = {}
    for person in persons:
        meeting_vars[person] = {
            "start": Int(f"{person}_start"),
            "end": Int(f"{person}_end"),
            "attend": Bool(f"{person}_attend")
        }
        # If we attend, the meeting must fall within the available time window and meet the duration minimum.
        opt.add(Implies(meeting_vars[person]["attend"],
                        And(meeting_vars[person]["start"] >= details[person]["avail_start"],
                            meeting_vars[person]["end"] <= details[person]["avail_end"],
                            meeting_vars[person]["end"] - meeting_vars[person]["start"] >= details[person]["min_duration"])))
        # If we do not attend, set start and end to 0.
        opt.add(Implies(Not(meeting_vars[person]["attend"]),
                        And(meeting_vars[person]["start"] == 0,
                            meeting_vars[person]["end"] == 0)))
        # Ensure that from the arrival location we can reach the meeting location.
        loc = details[person]["location"]
        travel_from_start = travel[(arrival_location, loc)]
        opt.add(Implies(meeting_vars[person]["attend"],
                        meeting_vars[person]["start"] >= arrival_time + travel_from_start))
    
    # For every pair of meetings, if both are attended, enforce that one meeting happens before the other accounting for travel.
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            p_i = persons[i]
            p_j = persons[j]
            loc_i = details[p_i]["location"]
            loc_j = details[p_j]["location"]
            t_i_j = travel[(loc_i, loc_j)]
            t_j_i = travel[(loc_j, loc_i)]
            cond_i_before_j = meeting_vars[p_i]["end"] + t_i_j <= meeting_vars[p_j]["start"]
            cond_j_before_i = meeting_vars[p_j]["end"] + t_j_i <= meeting_vars[p_i]["start"]
            opt.add(Implies(And(meeting_vars[p_i]["attend"], meeting_vars[p_j]["attend"]),
                            Or(cond_i_before_j, cond_j_before_i)))
    
    # Objective: maximize the number of attended meetings.
    total_meetings = Sum([If(meeting_vars[p]["attend"], 1, 0) for p in persons])
    opt.maximize(total_meetings)

    # Check for a solution and extract the model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Gather meetings that are attended and sort them by start time
        for person in persons:
            if is_true(model.evaluate(meeting_vars[person]["attend"])):
                start_val = model.evaluate(meeting_vars[person]["start"]).as_long()
                end_val = model.evaluate(meeting_vars[person]["end"]).as_long()
                itinerary.append((start_val, {
                    "action": "meet",
                    "location": details[person]["location"],
                    "person": person,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                }))
        itinerary.sort(key=lambda x: x[0])
        itinerary_list = [entry[1] for entry in itinerary]
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()