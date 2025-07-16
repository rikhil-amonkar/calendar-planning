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
    
    while remaining_friends:
        best_friend = None
        best_start_time = None
        best_end_time = None
        best_travel_time = None
        
        for name, (loc, start_str, end_str, min_duration) in remaining_friends.items():
            # Calculate travel time to this friend
            travel_time = travel_times[current_location][loc]
            
            # Calculate earliest possible arrival time
            earliest_arrival = current_time + travel_time
            friend_start = time_to_minutes(start_str)
            friend_end = time_to_minutes(end_str)
            
            # Determine when we can actually start the meeting
            meeting_start = max(earliest_arrival, friend_start)
            meeting_end = meeting_start + min_duration
            
            # Check if we can complete the meeting within friend's availability
            if meeting_end > friend_end:
                continue  # Can't meet this friend
            
            # Calculate total time including travel
            total_time = meeting_end - current_time
            
            # Choose the friend that allows earliest next meeting
            if best_friend is None or meeting_start < best_start_time:
                best_friend = name
                best_start_time = meeting_start
                best_end_time = meeting_end
                best_travel_time = travel_time
        
        if not best_friend:
            break  # No more friends can be visited
        
        # Add travel to itinerary if needed
        if current_location != friends[best_friend][0]:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": friends[best_friend][0],
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + best_travel_time)
            })
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": friends[best_friend][0],
            "person": best_friend,
            "start_time": minutes_to_time(best_start_time),
            "end_time": minutes_to_time(best_end_time)
        })
        
        # Update current location and time
        current_location = friends[best_friend][0]
        current_time = best_end_time
        del remaining_friends[best_friend]
    
    return itinerary

def main():
    itinerary = calculate_best_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()