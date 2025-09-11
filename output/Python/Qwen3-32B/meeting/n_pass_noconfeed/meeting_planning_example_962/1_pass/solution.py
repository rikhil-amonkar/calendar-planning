import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    friends = [
        {
            'name': 'Elizabeth',
            'location': 'Marina District',
            'start_time': 19 * 60,  # 7:00 PM
            'end_time': 20 * 60 + 45,  # 8:45 PM
            'required_duration': 105,
        },
        {
            'name': 'Joshua',
            'location': 'Presidio',
            'start_time': 8 * 60 + 30,  # 8:30 AM
            'end_time': 13 * 60 + 15,  # 1:15 PM
            'required_duration': 105,
        },
        {
            'name': 'Timothy',
            'location': 'North Beach',
            'start_time': 19 * 60 + 45,  # 7:45 PM
            'end_time': 22 * 60,  # 10:00 PM
            'required_duration': 90,
        },
        {
            'name': 'David',
            'location': 'Embarcadero',
            'start_time': 10 * 60 + 45,  # 10:45 AM
            'end_time': 12 * 60 + 30,  # 12:30 PM
            'required_duration': 30,
        },
        {
            'name': 'Kimberly',
            'location': 'Haight-Ashbury',
            'start_time': 16 * 60 + 45,  # 4:45 PM
            'end_time': 21 * 60 + 30,  # 9:30 PM
            'required_duration': 75,
        },
        {
            'name': 'Lisa',
            'location': 'Golden Gate Park',
            'start_time': 17 * 60 + 30,  # 5:30 PM
            'end_time': 21 * 60 + 45,  # 9:45 PM
            'required_duration': 45,
        },
        {
            'name': 'Stephanie',
            'location': 'Alamo Square',
            'start_time': 15 * 60 + 30,  # 3:30 PM
            'end_time': 16 * 60 + 30,  # 4:30 PM
            'required_duration': 30,
        },
        {
            'name': 'Helen',
            'location': 'Financial District',
            'start_time': 17 * 60 + 30,  # 5:30 PM
            'end_time': 18 * 60 + 30,  # 6:30 PM
            'required_duration': 45,
        },
        {
            'name': 'Laura',
            'location': 'Sunset District',
            'start_time': 17 * 60 + 45,  # 5:45 PM
            'end_time': 21 * 60 + 15,  # 9:15 PM
            'required_duration': 90,
        },
    ]

    travel_times = {
        'The Castro': {
            'Marina District': 21,
            'Presidio': 20,
            'North Beach': 20,
            'Embarcadero': 22,
            'Haight-Ashbury': 6,
            'Golden Gate Park': 11,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Sunset District': 17,
        },
        'Marina District': {
            'The Castro': 22,
            'Presidio': 10,
            'North Beach': 11,
            'Embarcadero': 14,
            'Haight-Ashbury': 16,
            'Golden Gate Park': 18,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Sunset District': 19,
        },
        'Presidio': {
            'The Castro': 21,
            'Marina District': 11,
            'North Beach': 18,
            'Embarcadero': 20,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 12,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Sunset District': 15,
        },
        'North Beach': {
            'The Castro': 23,
            'Marina District': 9,
            'Presidio': 17,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            'Golden Gate Park': 22,
            'Richmond District': 18,
            'Alamo Square': 16,
            'Financial District': 8,
            'Sunset District': 27,
        },
        'Embarcadero': {
            'The Castro': 25,
            'Marina District': 12,
            'Presidio': 20,
            'North Beach': 5,
            'Haight-Ashbury': 21,
            'Golden Gate Park': 25,
            'Richmond District': 21,
            'Alamo Square': 19,
            'Financial District': 5,
            'Sunset District': 30,
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'Marina District': 17,
            'Presidio': 15,
            'North Beach': 19,
            'Embarcadero': 20,
            'Golden Gate Park': 7,
            'Richmond District': 10,
            'Alamo Square': 5,
            'Financial District': 21,
            'Sunset District': 15,
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Marina District': 16,
            'Presidio': 11,
            'North Beach': 23,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Richmond District': 7,
            'Alamo Square': 9,
            'Financial District': 26,
            'Sunset District': 10,
        },
        'Richmond District': {
            'The Castro': 16,
            'Marina District': 9,
            'Presidio': 7,
            'North Beach': 17,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            'Golden Gate Park': 9,
            'Alamo Square': 13,
            'Financial District': 22,
            'Sunset District': 11,
        },
        'Alamo Square': {
            'The Castro': 8,
            'Marina District': 15,
            'Presidio': 17,
            'North Beach': 15,
            'Embarcadero': 16,
            'Haight-Ashbury': 5,
            'Golden Gate Park': 9,
            'Richmond District': 11,
            'Financial District': 17,
            'Sunset District': 16,
        },
        'Financial District': {
            'The Castro': 20,
            'Marina District': 15,
            'Presidio': 22,
            'North Beach': 7,
            'Embarcadero': 4,
            'Haight-Ashbury': 19,
            'Golden Gate Park': 23,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Sunset District': 30,
        },
        'Sunset District': {
            'The Castro': 17,
            'Marina District': 21,
            'Presidio': 16,
            'North Beach': 28,
            'Embarcadero': 30,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 11,
            'Richmond District': 12,
            'Alamo Square': 17,
            'Financial District': 30,
        },
    }

    num_friends = len(friends)
    best_itinerary = []
    best_length = 0

    def backtrack(current_location, current_time, visited, path):
        nonlocal best_itinerary, best_length

        current_length = len(path)
        if current_length > best_length:
            best_length = current_length
            best_itinerary = path.copy()

        for i in range(num_friends):
            if not (visited & (1 << i)):
                friend = friends[i]
                friend_loc = friend['location']
                travel_time = travel_times[current_location][friend_loc]
                arrival_time = current_time + travel_time

                start_meet = max(arrival_time, friend['start_time'])
                if start_meet + friend['required_duration'] <= friend['end_time']:
                    new_visited = visited | (1 << i)
                    new_path = path + [{
                        'action': 'meet',
                        'location': friend_loc,
                        'person': friend['name'],
                        'start_time': format_time(start_meet),
                        'end_time': format_time(start_meet + friend['required_duration']),
                    }]
                    backtrack(friend_loc, start_meet + friend['required_duration'], new_visited, new_path)

    # Start at The Castro at 9:00 AM (540 minutes)
    backtrack('The Castro', 9 * 60, 0, [])

    print(json.dumps({"itinerary": best_itinerary}))

if __name__ == "__main__":
    main()