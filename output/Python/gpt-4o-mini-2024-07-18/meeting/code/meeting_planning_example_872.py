import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("North Beach", "Chinatown"): 3,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Union Square", "Embarcadero"): 10,
    ("Financial District", "Embarcadero"): 4,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17
}

# Meeting constraints as tuples (person, location, start_time, end_time, min_duration)
constraints = [
    ("Karen", "Haight-Ashbury", "21:00", "21:45", 45),
    ("Jessica", "Nob Hill", "13:45", "21:00", 90),
    ("Brian", "Russian Hill", "15:30", "21:45", 60),
    ("Kenneth", "North Beach", "09:45", "21:00", 30),
    ("Jason", "Chinatown", "08:15", "11:45", 75),
    ("Stephanie", "Union Square", "14:45", "18:45", 105),
    ("Kimberly", "Embarcadero", "09:45", "19:30", 75),
    ("Steven", "Financial District", "07:15", "21:15", 60),
    ("Mark", "Marina District", "10:15", "13:00", 75)
]

def time_to_minutes(time_str):
    time = datetime.strptime(time_str, "%H:%M")
    return time.hour * 60 + time.minute

def minutes_to_time(minutes):
    hour, minute = divmod(minutes, 60)
    return f"{hour}:{minute:02}"

# Main scheduling algorithm
def schedule_meetings():
    start_time = time_to_minutes("9:00")
    end_time = time_to_minutes("21:45")
    
    # Resulting itinerary
    itinerary = []

    # Meeting Jason
    jason_start = time_to_minutes("08:15")
    jason_end = jason_start + 75
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Jason",
        "start_time": minutes_to_time(jason_start),
        "end_time": minutes_to_time(jason_end)
    })
    
    # Travel to Presidio from Chinatown
    travel_time = travel_times[("Chinatown", "Presidio")]
    presido_start_time = jason_end + travel_time
    if presido_start_time < start_time:
        presido_start_time = start_time

    # Meeting Kenneth
    kenneth_start = time_to_minutes("09:45")
    kenneth_end = kenneth_start + 30
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "Kenneth",
        "start_time": minutes_to_time(kenneth_start),
        "end_time": minutes_to_time(kenneth_end)
    })

    # Travel to Haight-Ashbury to meet Karen
    travel_time = travel_times[("North Beach", "Haight-Ashbury")]
    karen_start = max(21 * 60, presido_start_time + travel_time)  # arrive at the earliest allowed time
    karen_end = karen_start + 45
    itinerary.append({
        "action": "meet",
        "location": "Haight-Ashbury",
        "person": "Karen",
        "start_time": minutes_to_time(karen_start),
        "end_time": minutes_to_time(karen_end)
    })

    # Travel to Nob Hill for Jessica
    travel_time = travel_times[("Haight-Ashbury", "Nob Hill")]
    jessica_start = max(13 * 60 + 45, karen_end + travel_time)
    jessica_end = jessica_start + 90
    itinerary.append({
        "action": "meet",
        "location": "Nob Hill",
        "person": "Jessica",
        "start_time": minutes_to_time(jessica_start),
        "end_time": minutes_to_time(jessica_end)
    })

    # Travel to Russian Hill to meet Brian
    travel_time = travel_times[("Nob Hill", "Russian Hill")]
    brian_start = max(15 * 60 + 30, jessica_end + travel_time)
    brian_end = brian_start + 60
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Brian",
        "start_time": minutes_to_time(brian_start),
        "end_time": minutes_to_time(brian_end)
    })

    # Travel to Union Square to meet Stephanie
    travel_time = travel_times[("Russian Hill", "Union Square")]
    stephanie_start = max(14 * 60 + 45, brian_end + travel_time)
    stephanie_end = stephanie_start + 105
    itinerary.append({
        "action": "meet",
        "location": "Union Square",
        "person": "Stephanie",
        "start_time": minutes_to_time(stephanie_start),
        "end_time": minutes_to_time(stephanie_end)
    })

    # Travel to Embarcadero to meet Kimberly
    travel_time = travel_times[("Union Square", "Embarcadero")]
    kimberly_start = max(9 * 60 + 45, stephanie_end + travel_time)
    kimberly_end = kimberly_start + 75
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "Kimberly",
        "start_time": minutes_to_time(kimberly_start),
        "end_time": minutes_to_time(kimberly_end)
    })

    # Travel to Financial District to meet Steven
    travel_time = travel_times[("Embarcadero", "Financial District")]
    steven_start = max(7 * 60 + 15, kimberly_end + travel_time)
    steven_end = steven_start + 60
    itinerary.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Steven",
        "start_time": minutes_to_time(steven_start),
        "end_time": minutes_to_time(steven_end)
    })

    # Meeting Mark
    travel_time = travel_times[("Financial District", "Marina District")]
    mark_start = max(10 * 60 + 15, steven_end + travel_time)
    mark_end = mark_start + 75
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Mark",
        "start_time": minutes_to_time(mark_start),
        "end_time": minutes_to_time(mark_end)
    })

    return {"itinerary": itinerary}

solution = schedule_meetings()
print(json.dumps(solution, indent=2))