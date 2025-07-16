import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22
    }
}

# People data: name -> (location, available_start, available_end, min_duration)
people = {
    'Robert': ('Chinatown', 7.75, 17.5, 120),
    'David': ('Sunset District', 12.5, 19.75, 45),
    'Matthew': ('Alamo Square', 8.75, 13.75, 90),
    'Jessica': ('Financial District', 9.5, 18.75, 45),
    'Melissa': ('North Beach', 7.25, 16.75, 45),
    'Mark': ('Embarcadero', 15.25, 17.0, 45),
    'Deborah': ('Presidio', 19.0, 19.75, 45),
    'Karen': ('Golden Gate Park', 19.5, 22.0, 120),
    'Laura': ('Bayview', 21.25, 22.25, 15)
}

def time_to_float(time_str):
    if isinstance(time_str, float):
        return time_str
    h, m = map(int, time_str.split(':'))
    return h + m / 60.0

def float_to_time(time_float):
    h = int(time_float)
    m = int(round((time_float - h) * 60))
    if m == 60:
        h += 1
        m = 0
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc] / 60.0

def schedule_meeting(current_time, current_location, person, best_schedule, remaining_people):
    name, (location, avail_start, avail_end, min_duration) = person
    
    # Calculate travel time
    travel_time = get_travel_time(current_location, location)
    arrival_time = current_time + travel_time
    
    # Check if we can meet this person
    meeting_start = max(arrival_time, avail_start)
    meeting_end = meeting_start + min_duration / 60.0
    
    if meeting_end <= avail_end and meeting_end <= 24.0:
        new_schedule = best_schedule.copy()
        new_schedule.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": float_to_time(meeting_start),
            "end_time": float_to_time(meeting_end)
        })
        
        new_remaining = [p for p in remaining_people if p[0] != name]
        new_time = meeting_end
        new_location = location
        
        return new_time, new_location, new_schedule, new_remaining
    else:
        return None

def find_best_schedule(start_time, start_location, people_list):
    from collections import deque
    
    best_schedule = []
    best_count = 0
    
    # Try all permutations of the first 5 people to keep computation manageable
    for first_people in permutations(people_list, min(5, len(people_list))):
        queue = deque()
        initial_state = (start_time, start_location, [], list(people_list))
        queue.append(initial_state)
        
        while queue:
            current_time, current_location, current_schedule, remaining = queue.popleft()
            
            if len(current_schedule) > best_count:
                best_schedule = current_schedule
                best_count = len(current_schedule)
                if best_count == len(people_list):
                    return best_schedule
            
            for person in remaining:
                result = schedule_meeting(current_time, current_location, person, current_schedule, remaining)
                if result:
                    queue.append(result)
    
    return best_schedule

def main():
    start_time = time_to_float("9:00")
    start_location = "Richmond District"
    
    # Convert people to list of tuples (name, data)
    people_list = [(name, data) for name, data in people.items()]
    
    # Sort people by their availability window (earlier first)
    people_list.sort(key=lambda x: (x[1][1], x[1][2]))
    
    best_schedule = find_best_schedule(start_time, start_location, people_list)
    
    # Prepare output
    output = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()