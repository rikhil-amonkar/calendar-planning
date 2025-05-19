import json
from datetime import datetime, timedelta

# Define locations and travel times
travel_times = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# Define meeting constraints
meetings = {
    "Kenneth": {"location": "Richmond District", "start": "21:15", "end": "22:00", "duration": 30},
    "Lisa": {"location": "Union Square", "start": "09:00", "end": "16:30", "duration": 45},
    "Joshua": {"location": "Financial District", "start": "12:00", "end": "15:15", "duration": 15},
    "Nancy": {"location": "Pacific Heights", "start": "08:00", "end": "11:30", "duration": 90},
    "Andrew": {"location": "Nob Hill", "start": "11:30", "end": "20:15", "duration": 60},
    "John": {"location": "Bayview", "start": "16:45", "end": "21:30", "duration": 75},
}

# Function to compute schedule
def compute_schedule():
    itinerary = []
    current_time = datetime.strptime("09:00", "%H:%M")

    # Meet Nancy first as she is only available until 11:30
    if current_time < datetime.strptime(meetings["Nancy"]["end"], "%H:%M"):
        start_time = max(current_time, datetime.strptime(meetings["Nancy"]["start"], "%H:%M"))
        end_time = start_time + timedelta(minutes=meetings["Nancy"]["duration"])
        
        # Calculate travel time to the next location after Nancy
        travel_time = travel_times[("Pacific Heights", "Nob Hill")]
        current_time = end_time + timedelta(minutes=travel_time)

        itinerary.append({
            "action": "meet",
            "location": meetings["Nancy"]["location"],
            "person": "Nancy",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    # Meet Joshua next
    if current_time < datetime.strptime(meetings["Joshua"]["end"], "%H:%M"):
        start_time = max(current_time, datetime.strptime(meetings["Joshua"]["start"], "%H:%M"))
        end_time = start_time + timedelta(minutes=meetings["Joshua"]["duration"])

        # Calculate travel time to the next location after Joshua
        travel_time = travel_times[("Financial District", "Nob Hill")]
        current_time = end_time + timedelta(minutes=travel_time)

        itinerary.append({
            "action": "meet",
            "location": meetings["Joshua"]["location"],
            "person": "Joshua",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    # Meet Andrew next
    if current_time < datetime.strptime(meetings["Andrew"]["end"], "%H:%M"):
        start_time = max(current_time, datetime.strptime(meetings["Andrew"]["start"], "%H:%M"))
        end_time = start_time + timedelta(minutes=meetings["Andrew"]["duration"])

        # Calculate travel time to the next location after Andrew
        travel_time = travel_times[("Nob Hill", "Bayview")]
        current_time = end_time + timedelta(minutes=travel_time)

        itinerary.append({
            "action": "meet",
            "location": meetings["Andrew"]["location"],
            "person": "Andrew",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    # Meet Lisa next
    if current_time < datetime.strptime(meetings["Lisa"]["end"], "%H:%M"):
        start_time = max(current_time, datetime.strptime(meetings["Lisa"]["start"], "%H:%M"))
        end_time = start_time + timedelta(minutes=meetings["Lisa"]["duration"])

        # Calculate travel time to the next location after Lisa
        travel_time = travel_times[("Union Square", "Bayview")]
        current_time = end_time + timedelta(minutes=travel_time)

        itinerary.append({
            "action": "meet",
            "location": meetings["Lisa"]["location"],
            "person": "Lisa",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    # Meet Kenneth last
    if current_time < datetime.strptime(meetings["Kenneth"]["end"], "%H:%M"):
        start_time = max(current_time, datetime.strptime(meetings["Kenneth"]["start"], "%H:%M"))
        end_time = start_time + timedelta(minutes=meetings["Kenneth"]["duration"])

        itinerary.append({
            "action": "meet",
            "location": meetings["Kenneth"]["location"],
            "person": "Kenneth",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    return json.dumps({"itinerary": itinerary}, indent=2)

# Execute the program
if __name__ == "__main__":
    solution = compute_schedule()
    print(solution)