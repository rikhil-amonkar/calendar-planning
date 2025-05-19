import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str.endswith('AM') or time_str.endswith('PM'):
        time_str, period = time_str[:-2].strip(), time_str[-2:]
        hours, minutes = map(int, time_str.split(':'))
        if period == 'PM' and hours != 12:
            hours += 12
        elif period == 'AM' and hours == 12:
            hours = 0
    else:
        hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes
travel_times = {
    'Bayview': {
        'Russian Hill': 23,
        'Alamo Square': 16,
        'North Beach': 21,
        'Financial District': 19
    },
    'Russian Hill': {
        'Bayview': 23,
        'Alamo Square': 15,
        'North Beach': 5,
        'Financial District': 11
    },
    'Alamo Square': {
        'Bayview': 16,
        'Russian Hill': 13,
        'North Beach': 15,
        'Financial District': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Russian Hill': 4,
        'Alamo Square': 16,
        'Financial District': 8
    },
    'Financial District': {
        'Bayview': 19,
        'Russian Hill': 10,
        'Alamo Square': 17,
        'North Beach': 7
    }
}

# Constraints
constraints = {
    'Joseph': {
        'location': 'Russian Hill',
        'start': time_to_minutes('8:30AM'),
        'end': time_to_minutes('7:15PM'),
        'duration': 60
    },
    'Nancy': {
        'location': 'Alamo Square',
        'start': time_to_minutes('11:00AM'),
        'end': time_to_minutes('4:00PM'),
        'duration': 90
    },
    'Jason': {
        'location': 'North Beach',
        'start': time_to_minutes('4:45PM'),
        'end': time_to_minutes('9:45PM'),
        'duration': 15
    },
    'Jeffrey': {
        'location': 'Financial District',
        'start': time_to_minutes('10:30AM'),
        'end': time_to_minutes('3:45PM'),
        'duration': 45
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes('9:00AM')
    current_location = 'Bayview'
    schedule = []
    met_people = set()
    
    for person in order:
        if person in met_people:
            continue
        info = constraints[person]
        location = info['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, info['start'])
        meeting_end = meeting_start + info['duration']
        
        if meeting_end > info['end']:
            continue  # Can't meet this person
        
        # Add to schedule
        schedule.append({
            'person': person,
            'location': location,
            'start_time': meeting_start,
            'end_time': meeting_end,
            'duration': info['duration']
        })
        
        met_people.add(person)
        current_time = meeting_end
        current_location = location
    
    return schedule, len(met_people)

def find_optimal_schedule():
    people = list(constraints.keys())
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting people
    for order in permutations(people):
        schedule, count = calculate_schedule(order)
        if count > max_meetings or (count == max_meetings and len(best_schedule) == 0):
            best_schedule = schedule
            max_meetings = count
        elif count == max_meetings:
            # Prefer schedules that end earlier
            if schedule[-1]['end_time'] < best_schedule[-1]['end_time']:
                best_schedule = schedule
    
    return best_schedule

def format_schedule(schedule):
    itinerary = []
    for meeting in schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })
    return {"itinerary": itinerary}

optimal_schedule = find_optimal_schedule()
result = format_schedule(optimal_schedule)
print(json.dumps(result, indent=2))