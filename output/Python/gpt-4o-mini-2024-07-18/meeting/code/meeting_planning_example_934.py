import json
from datetime import datetime, timedelta

# Locations and travel times (in minutes)
travel_times = {
    "Nob Hill": {"Embarcadero": 10, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7, 
                 "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17, 
                 "Marina District": 11, "Russian Hill": 5},
    "Embarcadero": {"Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10, 
                    "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25, 
                    "Marina District": 12, "Russian Hill": 8},
    "The Castro": {"Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19, 
                   "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11, 
                   "Marina District": 21, "Russian Hill": 18},
    "Haight-Ashbury": {"Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19, 
                       "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7, 
                       "Marina District": 17, "Russian Hill": 17},
    "Union Square": {"Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18, 
                     "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22, 
                     "Marina District": 18, "Russian Hill": 13},
    "North Beach": {"Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18, 
                    "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22, 
                    "Marina District": 9, "Russian Hill": 4},
    "Pacific Heights": {"Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11, 
                        "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15, 
                        "Marina District": 6, "Russian Hill": 7},
    "Chinatown": {"Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19, 
                  "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23, 
                  "Marina District": 12, "Russian Hill": 7},
    "Golden Gate Park": {"Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7, 
                         "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23, 
                         "Marina District": 16, "Russian Hill": 19},
    "Marina District": {"Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16, 
                        "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15, 
                        "Golden Gate Park": 18, "Russian Hill": 8},
    "Russian Hill": {"Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17, 
                     "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9, 
                     "Golden Gate Park": 21, "Marina District": 7}
}

# Meeting constraints
meetings = {
    "Mary": {"location": "Embarcadero", "start": "20:00", "end": "21:15", "duration": 75},
    "Kenneth": {"location": "The Castro", "start": "11:15", "end": "19:15", "duration": 30},
    "Joseph": {"location": "Haight-Ashbury", "start": "20:00", "end": "22:00", "duration": 120},
    "Sarah": {"location": "Union Square", "start": "11:45", "end": "14:30", "duration": 90},
    "Thomas": {"location": "North Beach", "start": "19:15", "end": "19:45", "duration": 15},
    "Daniel": {"location": "Pacific Heights", "start": "13:45", "end": "20:30", "duration": 15},
    "Richard": {"location": "Chinatown", "start": "08:00", "end": "18:45", "duration": 30},
    "Mark": {"location": "Golden Gate Park", "start": "17:30", "end": "21:30", "duration": 120},
    "David": {"location": "Marina District", "start": "20:00", "end": "21:00", "duration": 60},
    "Karen": {"location": "Russian Hill", "start": "13:15", "end": "18:30", "duration": 120},
}

# Start time at Nob Hill
start_time = datetime.strptime("09:00", "%H:%M")

# Function to find the optimal meeting schedule
def find_optimal_schedule():
    schedule = []
    current_time = start_time

    # Meet Richard first
    richard_meeting = meetings["Richard"]
    end_time_richard = current_time + timedelta(minutes=richard_meeting["duration"])
    if end_time_richard < datetime.strptime(richard_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": richard_meeting["location"],
            "person": "Richard",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_richard.strftime("%H:%M"),
        })
        current_time = end_time_richard + timedelta(minutes=travel_times["Nob Hill"][richard_meeting["location"]])
    
    # Meet Sarah
    sarah_meeting = meetings["Sarah"]
    travel_time_to_sarah = travel_times["Nob Hill"][sarah_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_sarah)
    end_time_sarah = current_time + timedelta(minutes=sarah_meeting["duration"])
    if end_time_sarah < datetime.strptime(sarah_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": sarah_meeting["location"],
            "person": "Sarah",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_sarah.strftime("%H:%M"),
        })
        current_time = end_time_sarah + timedelta(minutes=travel_times[sarah_meeting["location"]]["Pacific Heights"])

    # Meet Daniel
    daniel_meeting = meetings["Daniel"]
    travel_time_to_daniel = travel_times["Union Square"][daniel_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_daniel)
    end_time_daniel = current_time + timedelta(minutes=daniel_meeting["duration"])
    if end_time_daniel < datetime.strptime(daniel_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": daniel_meeting["location"],
            "person": "Daniel",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_daniel.strftime("%H:%M"),
        })
        current_time = end_time_daniel + timedelta(minutes=travel_times[daniel_meeting["location"]]["North Beach"])

    # Meet Thomas
    thomas_meeting = meetings["Thomas"]
    travel_time_to_thomas = travel_times["Pacific Heights"][thomas_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_thomas)
    end_time_thomas = current_time + timedelta(minutes=thomas_meeting["duration"])
    if end_time_thomas < datetime.strptime(thomas_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": thomas_meeting["location"],
            "person": "Thomas",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_thomas.strftime("%H:%M"),
        })
        current_time = end_time_thomas + timedelta(minutes=travel_times[thomas_meeting["location"]]["Golden Gate Park"])

    # Meet Kenneth
    kenneth_meeting = meetings["Kenneth"]
    travel_time_to_kenneth = travel_times["Nob Hill"][kenneth_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_kenneth)
    end_time_kenneth = current_time + timedelta(minutes=kenneth_meeting["duration"])
    if end_time_kenneth < datetime.strptime(kenneth_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": kenneth_meeting["location"],
            "person": "Kenneth",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_kenneth.strftime("%H:%M"),
        })
        current_time = end_time_kenneth + timedelta(minutes=travel_times[kenneth_meeting["location"]]["Nob Hill"])

    # Meet Mary
    mary_meeting = meetings["Mary"]
    travel_time_to_mary = travel_times["Nob Hill"][mary_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_mary)
    end_time_mary = current_time + timedelta(minutes=mary_meeting["duration"])
    if end_time_mary < datetime.strptime(mary_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": mary_meeting["location"],
            "person": "Mary",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_mary.strftime("%H:%M"),
        })
        current_time = end_time_mary

    # Meet Joseph
    joseph_meeting = meetings["Joseph"]
    travel_time_to_joseph = travel_times["Nob Hill"][joseph_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_joseph)
    end_time_joseph = current_time + timedelta(minutes=joseph_meeting["duration"])
    if end_time_joseph < datetime.strptime(joseph_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": joseph_meeting["location"],
            "person": "Joseph",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_joseph.strftime("%H:%M"),
        })
        current_time = end_time_joseph

    # Meet Karen
    karen_meeting = meetings["Karen"]
    travel_time_to_karen = travel_times["Pacific Heights"][karen_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_karen)
    end_time_karen = current_time + timedelta(minutes=karen_meeting["duration"])
    if end_time_karen < datetime.strptime(karen_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": karen_meeting["location"],
            "person": "Karen",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_karen.strftime("%H:%M"),
        })
        current_time = end_time_karen

    # Meet Mark
    mark_meeting = meetings["Mark"]
    travel_time_to_mark = travel_times["Nob Hill"][mark_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_mark)
    end_time_mark = current_time + timedelta(minutes=mark_meeting["duration"])
    if end_time_mark < datetime.strptime(mark_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": mark_meeting["location"],
            "person": "Mark",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_mark.strftime("%H:%M"),
        })

    # Meet David
    david_meeting = meetings["David"]
    travel_time_to_david = travel_times["Golden Gate Park"][david_meeting["location"]]
    current_time += timedelta(minutes=travel_time_to_david)
    end_time_david = current_time + timedelta(minutes=david_meeting["duration"])
    if end_time_david < datetime.strptime(david_meeting["end"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": david_meeting["location"],
            "person": "David",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": end_time_david.strftime("%H:%M"),
        })

    return {"itinerary": schedule}

# Generating the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result as JSON
print(json.dumps(optimal_schedule, indent=2))