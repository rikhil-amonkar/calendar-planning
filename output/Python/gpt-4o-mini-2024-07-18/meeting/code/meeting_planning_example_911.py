import json
from datetime import datetime, timedelta

# Travel times (in minutes) represented as a dictionary of dictionaries
travel_times = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21,
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26,
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21,
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22,
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9,
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17,
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23,
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9,
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9,
    },
}

# Schedule constraints
constraints = {
    "Steven": {
        "location": "North Beach",
        "start": "17:30",
        "end": "20:30",
        "duration": 15,
    },
    "Sarah": {
        "location": "Golden Gate Park",
        "start": "17:00",
        "end": "19:15",
        "duration": 75,
    },
    "Brian": {
        "location": "Embarcadero",
        "start": "14:15",
        "end": "16:00",
        "duration": 105,
    },
    "Stephanie": {
        "location": "Haight-Ashbury",
        "start": "10:15",
        "end": "12:15",
        "duration": 75,
    },
    "Melissa": {
        "location": "Richmond District",
        "start": "14:00",
        "end": "19:30",
        "duration": 30,
    },
    "Nancy": {
        "location": "Nob Hill",
        "start": "08:15",
        "end": "12:45",
        "duration": 90,
    },
    "David": {
        "location": "Marina District",
        "start": "11:15",
        "end": "13:15",
        "duration": 120,
    },
    "James": {
        "location": "Presidio",
        "start": "15:00",
        "end": "18:15",
        "duration": 120,
    },
    "Elizabeth": {
        "location": "Union Square",
        "start": "11:30",
        "end": "21:00",
        "duration": 60,
    },
    "Robert": {
        "location": "Financial District",
        "start": "13:15",
        "end": "15:15",
        "duration": 45,
    },
}

# Function to convert time string to a datetime object
def time_to_datetime(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Function to convert datetime object to a time string
def datetime_to_time(dt):
    return dt.strftime("%H:%M")

# Function to find the optimal meeting schedule
def find_optimal_schedule():
    current_time = time_to_datetime("9:00")
    itinerary = []

    # Meeting with Nancy
    nancy_end_time = current_time + timedelta(minutes=90)
    itinerary.append({
        "action": "meet",
        "location": "Nob Hill",
        "person": "Nancy",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(nancy_end_time),
    })
    current_time = nancy_end_time + timedelta(minutes=travel_times["The Castro"]["Nob Hill"])

    # Meeting with Stephanie
    stephanie_end_time = current_time + timedelta(minutes=75)
    itinerary.append({
        "action": "meet",
        "location": "Haight-Ashbury",
        "person": "Stephanie",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(stephanie_end_time),
    })
    current_time = stephanie_end_time + timedelta(minutes=travel_times["Nob Hill"]["Haight-Ashbury"])

    # Meeting with David
    david_end_time = current_time + timedelta(minutes=120)
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "David",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(david_end_time),
    })
    current_time = david_end_time + timedelta(minutes=travel_times["Haight-Ashbury"]["Marina District"])

    # Meeting with Brian
    brian_end_time = current_time + timedelta(minutes=105)
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "Brian",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(brian_end_time),
    })
    current_time = brian_end_time + timedelta(minutes=travel_times["Marina District"]["Embarcadero"])

    # Meeting with Robert
    robert_end_time = current_time + timedelta(minutes=45)
    itinerary.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Robert",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(robert_end_time),
    })
    current_time = robert_end_time + timedelta(minutes=travel_times["Embarcadero"]["Financial District"])

    # Meeting with James
    # Arrive at Presidio by 15:00
    current_time = time_to_datetime("15:00")
    james_end_time = current_time + timedelta(minutes=120)
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "James",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(james_end_time),
    })
    current_time = james_end_time + timedelta(minutes=travel_times["Presidio"]["Financial District"])

    # Meeting with Sarah
    current_time = time_to_datetime("17:00")
    sarah_end_time = current_time + timedelta(minutes=75)
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Sarah",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(sarah_end_time),
    })
    current_time = sarah_end_time + timedelta(minutes=travel_times["Golden Gate Park"]["Nob Hill"])

    # Meeting with Steven
    current_time = time_to_datetime("17:30")
    steven_end_time = current_time + timedelta(minutes=15)
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "Steven",
        "start_time": datetime_to_time(current_time),
        "end_time": datetime_to_time(steven_end_time),
    })

    return {"itinerary": itinerary}

# Find the optimal schedule
optimal_schedule = find_optimal_schedule()

# Output the result in JSON format
print(json.dumps(optimal_schedule, indent=2))