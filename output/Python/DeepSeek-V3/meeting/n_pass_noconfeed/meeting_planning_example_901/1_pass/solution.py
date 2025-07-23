import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Russian Hill': {
        'Pacific Heights': 7,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Mission District': 16,
        'Alamo Square': 15,
        'Bayview': 23,
        'Richmond District': 14
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'North Beach': 9,
        'Golden Gate Park': 15,
        'Embarcadero': 10,
        'Haight-Ashbury': 11,
        'Fisherman\'s Wharf': 13,
        'Mission District': 15,
        'Alamo Square': 10,
        'Bayview': 22,
        'Richmond District': 12
    },
    'North Beach': {
        'Russian Hill': 4,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Alamo Square': 16,
        'Bayview': 25,
        'Richmond District': 18
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Pacific Heights': 16,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Fisherman\'s Wharf': 24,
        'Mission District': 17,
        'Alamo Square': 9,
        'Bayview': 23,
        'Richmond District': 7
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Pacific Heights': 11,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Alamo Square': 19,
        'Bayview': 21,
        'Richmond District': 21
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Pacific Heights': 12,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11,
        'Alamo Square': 5,
        'Bayview': 18,
        'Richmond District': 10
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Pacific Heights': 12,
        'North Beach': 6,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Alamo Square': 21,
        'Bayview': 26,
        'Richmond District': 18
    },
    'Mission District': {
        'Russian Hill': 15,
        'Pacific Heights': 16,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 12,
        'Fisherman\'s Wharf': 22,
        'Alamo Square': 11,
        'Bayview': 14,
        'Richmond District': 20
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Bayview': 16,
        'Richmond District': 11
    },
    'Bayview': {
        'Russian Hill': 23,
        'Pacific Heights': 23,
        'North Beach': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 19,
        'Haight-Ashbury': 19,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Alamo Square': 16,
        'Richmond District': 25
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Fisherman\'s Wharf': 18,
        'Mission District': 20,
        'Alamo Square': 13,
        'Bayview': 27
    }
}

# Person constraints
people = {
    'Emily': {
        'location': 'Pacific Heights',
        'start': '9:15',
        'end': '13:45',
        'min_duration': 120
    },
    'Helen': {
        'location': 'North Beach',
        'start': '13:45',
        'end': '18:45',
        'min_duration': 30
    },
    'Kimberly': {
        'location': 'Golden Gate Park',
        'start': '18:45',
        'end': '21:15',
        'min_duration': 75
    },
    'James': {
        'location': 'Embarcadero',
        'start': '10:30',
        'end': '11:30',
        'min_duration': 30
    },
    'Linda': {
        'location': 'Haight-Ashbury',
        'start': '7:30',
        'end': '19:15',
        'min_duration': 15
    },
    'Paul': {
        'location': 'Fisherman\'s Wharf',
        'start': '14:45',
        'end': '18:45',
        'min_duration': 90
    },
    'Anthony': {
        'location': 'Mission District',
        'start': '8:00',
        'end': '14:45',
        'min_duration': 105
    },
    'Nancy': {
        'location': 'Alamo Square',
        'start': '8:30',
        'end': '13:45',
        'min_duration': 120
    },
    'William': {
        'location': 'Bayview',
        'start': '17:30',
        'end': '20:30',
        'min_duration': 120
    },
    'Margaret': {
        'location': 'Richmond District',
        'start': '15:15',
        'end': '18:15',
        'min_duration': 45
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def can_meet(person, start_time, end_time):
    person_start = time_to_minutes(people[person]['start'])
    person_end = time_to_minutes(people[person]['end'])
    return (start_time >= person_start) and (end_time <= person_end) and (end_time - start_time >= people[person]['min_duration'])

def generate_schedule():
    current_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'
    itinerary = []
    
    # Priority order: James, Nancy, Anthony, Emily, Margaret, Paul, Helen, William, Kimberly, Linda
    priority_order = ['James', 'Nancy', 'Anthony', 'Emily', 'Margaret', 'Paul', 'Helen', 'William', 'Kimberly', 'Linda']
    
    for person in priority_order:
        loc = people[person]['location']
        travel_time = get_travel_time(current_location, loc)
        arrival_time = current_time + travel_time
        
        start_time = max(arrival_time, time_to_minutes(people[person]['start']))
        end_time = start_time + people[person]['min_duration']
        
        if can_meet(person, start_time, end_time):
            itinerary.append({
                'action': 'meet',
                'location': loc,
                'person': person,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            current_time = end_time
            current_location = loc
    
    return itinerary

def main():
    itinerary = generate_schedule()
    result = {
        'itinerary': itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()