import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    'Russian Hill': {
        'Sunset District': 23,
        'Union Square': 10,
        'Nob Hill': 5,
        'Marina District': 7,
        'Richmond District': 14,
        'Financial District': 11,
        'Embarcadero': 8,
        'The Castro': 21,
        'Alamo Square': 15,
        'Presidio': 14
    },
    'Sunset District': {
        'Russian Hill': 24,
        'Union Square': 30,
        'Nob Hill': 27,
        'Marina District': 21,
        'Richmond District': 12,
        'Financial District': 30,
        'Embarcadero': 30,
        'The Castro': 17,
        'Alamo Square': 17,
        'Presidio': 16
    },
    'Union Square': {
        'Russian Hill': 13,
        'Sunset District': 27,
        'Nob Hill': 9,
        'Marina District': 18,
        'Richmond District': 20,
        'Financial District': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Alamo Square': 15,
        'Presidio': 24
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Sunset District': 24,
        'Union Square': 7,
        'Marina District': 11,
        'Richmond District': 14,
        'Financial District': 9,
        'Embarcadero': 9,
        'The Castro': 17,
        'Alamo Square': 11,
        'Presidio': 17
    },
    'Marina District': {
        'Russian Hill': 8,
        'Sunset District': 19,
        'Union Square': 16,
        'Nob Hill': 12,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 14,
        'The Castro': 22,
        'Alamo Square': 15,
        'Presidio': 10
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Sunset District': 11,
        'Union Square': 21,
        'Nob Hill': 17,
        'Marina District': 9,
        'Financial District': 22,
        'Embarcadero': 19,
        'The Castro': 16,
        'Alamo Square': 13,
        'Presidio': 7
    },
    'Financial District': {
        'Russian Hill': 11,
        'Sunset District': 30,
        'Union Square': 9,
        'Nob Hill': 8,
        'Marina District': 15,
        'Richmond District': 21,
        'Embarcadero': 4,
        'The Castro': 20,
        'Alamo Square': 17,
        'Presidio': 22
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Sunset District': 30,
        'Union Square': 10,
        'Nob Hill': 10,
        'Marina District': 12,
        'Richmond District': 21,
        'Financial District': 5,
        'The Castro': 25,
        'Alamo Square': 19,
        'Presidio': 20
    },
    'The Castro': {
        'Russian Hill': 18,
        'Sunset District': 17,
        'Union Square': 19,
        'Nob Hill': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Financial District': 21,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Presidio': 20
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Sunset District': 16,
        'Union Square': 14,
        'Nob Hill': 11,
        'Marina District': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 16,
        'The Castro': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Russian Hill': 14,
        'Sunset District': 15,
        'Union Square': 22,
        'Nob Hill': 18,
        'Marina District': 11,
        'Richmond District': 7,
        'Financial District': 23,
        'Embarcadero': 20,
        'The Castro': 21,
        'Alamo Square': 19
    }
}

# Constraints
constraints = {
    'David': {'start': 9 * 60 + 15, 'end': 10 * 60, 'duration': 15},
    'Kenneth': {'start': 21 * 60, 'end': 21 * 60 + 30, 'duration': 15},
    'Patricia': {'start': 15 * 60, 'end': 19 * 60 + 15, 'duration': 120},
    'Mary': {'start': 15 * 60, 'end': 18 * 60, 'duration': 45},
    'Charles': {'start': 17 * 60, 'end': 21 * 60, 'duration': 15},
    'Joshua': {'start': 14 * 60, 'end': 17 * 60, 'duration': 90},
    'Ronald': {'start': 18 * 60, 'end': 21 * 60, 'duration': 30},
    'George': {'start': 14 * 60, 'end': 19 * 60, 'duration': 105},
    'Kimberly': {'start': 9 * 60, 'end': 14 * 60, 'duration': 105},
    'William': {'start': 7 * 60, 'end': 12 * 60, 'duration': 60}
}

def compute_meeting_schedule(constraints):
    # Initialize schedule
    schedule = []
    current_time = 9 * 60  # 9:00 AM

    # Add meeting with Kimberly
    schedule.append({'action':'meet', 'location': 'Russian Hill', 'person': 'Kimberly','start_time': '09:00', 'end_time': '10:45'})
    current_time += 105

    # Add meeting with William
    schedule.append({'action':'meet', 'location': 'Presidio', 'person': 'William','start_time': '10:45', 'end_time': '11:45'})
    current_time += 60

    # Add meeting with David
    start_time = max(current_time, constraints['David']['start'])
    end_time = min(start_time + constraints['David']['duration'], constraints['David']['end'])
    schedule.append({'action':'meet', 'location': 'Sunset District', 'person': 'David','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Joshua
    start_time = max(current_time, constraints['Joshua']['start'])
    end_time = min(start_time + constraints['Joshua']['duration'], constraints['Joshua']['end'])
    schedule.append({'action':'meet', 'location': 'Financial District', 'person': 'Joshua','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Mary
    start_time = max(current_time, constraints['Mary']['start'])
    end_time = min(start_time + constraints['Mary']['duration'], constraints['Mary']['end'])
    schedule.append({'action':'meet', 'location': 'Marina District', 'person': 'Mary','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Patricia
    start_time = max(current_time, constraints['Patricia']['start'])
    end_time = min(start_time + constraints['Patricia']['duration'], constraints['Patricia']['end'])
    schedule.append({'action':'meet', 'location': 'Nob Hill', 'person': 'Patricia','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Ronald
    start_time = max(current_time, constraints['Ronald']['start'])
    end_time = min(start_time + constraints['Ronald']['duration'], constraints['Ronald']['end'])
    schedule.append({'action':'meet', 'location': 'Embarcadero', 'person': 'Ronald','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with George
    start_time = max(current_time, constraints['George']['start'])
    end_time = min(start_time + constraints['George']['duration'], constraints['George']['end'])
    schedule.append({'action':'meet', 'location': 'The Castro', 'person': 'George','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Charles
    start_time = max(current_time, constraints['Charles']['start'])
    end_time = min(start_time + constraints['Charles']['duration'], constraints['Charles']['end'])
    schedule.append({'action':'meet', 'location': 'Richmond District', 'person': 'Charles','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})
    current_time = end_time

    # Add meeting with Kenneth
    start_time = max(current_time, constraints['Kenneth']['start'])
    end_time = min(start_time + constraints['Kenneth']['duration'], constraints['Kenneth']['end'])
    schedule.append({'action':'meet', 'location': 'Union Square', 'person': 'Kenneth','start_time': datetime.fromtimestamp(start_time).strftime('%H:%M'), 'end_time': datetime.fromtimestamp(end_time).strftime('%H:%M')})

    return schedule

def main():
    schedule = compute_meeting_schedule(constraints)
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()