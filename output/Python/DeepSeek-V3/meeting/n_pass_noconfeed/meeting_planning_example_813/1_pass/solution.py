import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Sunset District': 19,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Sunset District': 23,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Sunset District': 27,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 12,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Sunset District': 29,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21,
        'Embarcadero': 30,
        'Bayview': 22,
        'Union Square': 30,
        'Chinatown': 30,
        'Golden Gate Park': 11,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Sunset District': 10,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17
    },
    'Financial District': {
        'Marina District': 15,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Sunset District': 30,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Sunset District': 15,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11
    },
    'Mission District': {
        'Marina District': 19,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Sunset District': 24,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12
    }
}

# People data: name -> (location, available_start, available_end, min_duration)
people = {
    'Joshua': ('Embarcadero', '9:45', '18:00', 105),
    'Jeffrey': ('Bayview', '9:45', '20:15', 75),
    'Charles': ('Union Square', '10:45', '20:15', 120),
    'Joseph': ('Chinatown', '7:00', '15:30', 60),
    'Elizabeth': ('Sunset District', '9:00', '9:45', 45),
    'Matthew': ('Golden Gate Park', '11:00', '19:30', 45),
    'Carol': ('Financial District', '10:45', '11:15', 15),
    'Paul': ('Haight-Ashbury', '19:15', '20:30', 15),
    'Rebecca': ('Mission District', '17:00', '21:45', 45)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule_meeting(current_location, current_time, person, best_schedule=None):
    name, (location, start_str, end_str, duration) = person
    start = time_to_minutes(start_str)
    end = time_to_minutes(end_str)
    
    # Check if we've already scheduled this person in a better way
    if best_schedule:
        for entry in best_schedule:
            if entry['person'] == name:
                return None
    
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    
    # Can't arrive before they're available
    if arrival_time < start:
        arrival_time = start
    
    # Can't arrive after their availability ends minus duration
    if arrival_time > end - duration:
        return None
    
    meeting_end = arrival_time + duration
    return {
        'action': 'meet',
        'location': location,
        'person': name,
        'start_time': minutes_to_time(arrival_time),
        'end_time': minutes_to_time(meeting_end)
    }, location, meeting_end

def find_best_schedule():
    best_schedule = []
    best_count = 0
    
    # Try different orders of people to meet
    for order in permutations(people.items(), len(people)):
        current_location = 'Marina District'
        current_time = time_to_minutes('9:00')
        schedule = []
        
        for person in order:
            result = can_schedule_meeting(current_location, current_time, person)
            if result:
                meeting, new_location, new_time = result
                schedule.append(meeting)
                current_location = new_location
                current_time = new_time
        
        if len(schedule) > best_count:
            best_schedule = schedule
            best_count = len(schedule)
    
    return best_schedule

def main():
    best_schedule = find_best_schedule()
    
    # Convert to JSON
    output = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()