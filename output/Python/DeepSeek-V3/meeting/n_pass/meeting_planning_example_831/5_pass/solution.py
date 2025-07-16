import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Alamo Square': 19,
        'Financial District': 23,
        'Union Square': 22,
        'Sunset District': 15,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Alamo Square': 21,
        'Financial District': 11,
        'Union Square': 13,
        'Sunset District': 27,
        'Embarcadero': 8,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Richmond District': 18
    },
    'Alamo Square': {
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Financial District': 17,
        'Union Square': 14,
        'Sunset District': 16,
        'Embarcadero': 16,
        'Golden Gate Park': 9,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Financial District': {
        'Presidio': 22,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 17,
        'Union Square': 9,
        'Sunset District': 30,
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Richmond District': 21
    },
    'Union Square': {
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Alamo Square': 15,
        'Financial District': 9,
        'Sunset District': 27,
        'Embarcadero': 11,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Richmond District': 20
    },
    'Sunset District': {
        'Presidio': 16,
        'Fisherman\'s Wharf': 29,
        'Alamo Square': 17,
        'Financial District': 30,
        'Union Square': 30,
        'Embarcadero': 30,
        'Golden Gate Park': 11,
        'Chinatown': 30,
        'Richmond District': 12
    },
    'Embarcadero': {
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Alamo Square': 19,
        'Financial District': 5,
        'Union Square': 10,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Chinatown': 7,
        'Richmond District': 21
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Fisherman\'s Wharf': 24,
        'Alamo Square': 9,
        'Financial District': 26,
        'Union Square': 22,
        'Sunset District': 10,
        'Embarcadero': 25,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Presidio': 19,
        'Fisherman\'s Wharf': 8,
        'Alamo Square': 17,
        'Financial District': 5,
        'Union Square': 7,
        'Sunset District': 29,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Presidio': 7,
        'Fisherman\'s Wharf': 18,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Sunset District': 11,
        'Embarcadero': 19,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

# Friends data: name -> (location, start, end, min_duration)
friends = {
    'Jeffrey': ('Fisherman\'s Wharf', '10:15', '13:00', 90),
    'Ronald': ('Alamo Square', '7:45', '14:45', 120),
    'Jason': ('Financial District', '10:45', '16:00', 105),
    'Melissa': ('Union Square', '17:45', '18:15', 15),
    'Elizabeth': ('Sunset District', '14:45', '17:30', 105),
    'Margaret': ('Embarcadero', '13:15', '19:00', 90),
    'George': ('Golden Gate Park', '19:00', '22:00', 75),
    'Richard': ('Chinatown', '9:30', '21:00', 15),
    'Laura': ('Richmond District', '9:45', '18:00', 60)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_best_schedule():
    current_location = 'Presidio'
    current_time = time_to_minutes('9:00')
    remaining_friends = {k: v for k, v in friends.items()}
    itinerary = []
    
    # First meeting - Ronald at Alamo Square
    ronald_loc, ronald_start, ronald_end, ronald_dur = friends['Ronald']
    travel_time = travel_times[current_location][ronald_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(ronald_start))
    meeting_end = meeting_start + ronald_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": ronald_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": ronald_loc,
        "person": "Ronald",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = ronald_loc
    current_time = meeting_end
    del remaining_friends['Ronald']
    
    # Next - Laura at Richmond District
    laura_loc, laura_start, laura_end, laura_dur = friends['Laura']
    travel_time = travel_times[current_location][laura_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(laura_start))
    meeting_end = meeting_start + laura_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": laura_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": laura_loc,
        "person": "Laura",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = laura_loc
    current_time = meeting_end
    del remaining_friends['Laura']
    
    # Next - Richard at Chinatown
    richard_loc, richard_start, richard_end, richard_dur = friends['Richard']
    travel_time = travel_times[current_location][richard_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(richard_start))
    meeting_end = meeting_start + richard_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": richard_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": richard_loc,
        "person": "Richard",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = richard_loc
    current_time = meeting_end
    del remaining_friends['Richard']
    
    # Next - Jason at Financial District
    jason_loc, jason_start, jason_end, jason_dur = friends['Jason']
    travel_time = travel_times[current_location][jason_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(jason_start))
    meeting_end = meeting_start + jason_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": jason_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": jason_loc,
        "person": "Jason",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = jason_loc
    current_time = meeting_end
    del remaining_friends['Jason']
    
    # Next - Margaret at Embarcadero (moving this earlier to fit her availability)
    margaret_loc, margaret_start, margaret_end, margaret_dur = friends['Margaret']
    travel_time = travel_times[current_location][margaret_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(margaret_start))
    meeting_end = meeting_start + margaret_dur
    
    # Ensure meeting ends by Margaret's end time
    if meeting_end > time_to_minutes(margaret_end):
        meeting_start = time_to_minutes(margaret_end) - margaret_dur
        meeting_end = time_to_minutes(margaret_end)
        current_time = meeting_start - travel_time
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": margaret_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": margaret_loc,
        "person": "Margaret",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = margaret_loc
    current_time = meeting_end
    del remaining_friends['Margaret']
    
    # Next - Elizabeth at Sunset District
    elizabeth_loc, elizabeth_start, elizabeth_end, elizabeth_dur = friends['Elizabeth']
    travel_time = travel_times[current_location][elizabeth_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(elizabeth_start))
    meeting_end = meeting_start + elizabeth_dur
    
    # Check if meeting would end after Elizabeth's availability
    if meeting_end > time_to_minutes(elizabeth_end):
        # Adjust to fit within her window
        meeting_start = time_to_minutes(elizabeth_end) - elizabeth_dur
        meeting_end = time_to_minutes(elizabeth_end)
        current_time = meeting_start - travel_time
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": elizabeth_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": elizabeth_loc,
        "person": "Elizabeth",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = elizabeth_loc
    current_time = meeting_end
    del remaining_friends['Elizabeth']
    
    # Next - Melissa at Union Square
    melissa_loc, melissa_start, melissa_end, melissa_dur = friends['Melissa']
    travel_time = travel_times[current_location][melissa_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(melissa_start))
    meeting_end = meeting_start + melissa_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": melissa_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": melissa_loc,
        "person": "Melissa",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    current_location = melissa_loc
    current_time = meeting_end
    del remaining_friends['Melissa']
    
    # Final - George at Golden Gate Park
    george_loc, george_start, george_end, george_dur = friends['George']
    travel_time = travel_times[current_location][george_loc]
    meeting_start = max(current_time + travel_time, time_to_minutes(george_start))
    meeting_end = meeting_start + george_dur
    
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": george_loc,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(current_time + travel_time)
    })
    
    itinerary.append({
        "action": "meet",
        "location": george_loc,
        "person": "George",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    return itinerary

def main():
    itinerary = calculate_best_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()