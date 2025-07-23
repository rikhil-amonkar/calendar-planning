import itertools
import json

def main():
    travel_matrix = {
        "The Castro": {
            "Alamo Square": 8,
            "Richmond District": 16,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 24,
            "Marina District": 21,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Pacific Heights": 16,
            "Golden Gate Park": 11
        },
        "Alamo Square": {
            "The Castro": 8,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 14,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Haight-Ashbury": 5,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Richmond District": {
            "The Castro": 16,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Fisherman's Wharf": 18,
            "Marina District": 9,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "The Castro": 20,
            "Alamo Square": 17,
            "Richmond District": 21,
            "Union Square": 9,
            "Fisherman's Wharf": 10,
            "Marina District": 15,
            "Haight-Ashbury": 19,
            "Mission District": 17,
            "Pacific Heights": 13,
            "Golden Gate Park": 23
        },
        "Union Square": {
            "The Castro": 17,
            "Alamo Square": 15,
            "Richmond District": 20,
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Marina District": 18,
            "Haight-Ashbury": 18,
            "Mission District": 14,
            "Pacific Heights": 15,
            "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "The Castro": 27,
            "Alamo Square": 21,
            "Richmond District": 18,
            "Financial District": 11,
            "Union Square": 13,
            "Marina District": 9,
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Pacific Heights": 12,
            "Golden Gate Park": 25
        },
        "Marina District": {
            "The Castro": 22,
            "Alamo Square": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 16,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 16,
            "Mission District": 20,
            "Pacific Heights": 7,
            "Golden Gate Park": 18
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Alamo Square": 5,
            "Richmond District": 10,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 23,
            "Marina District": 17,
            "Mission District": 11,
            "Pacific Heights": 12,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "The Castro": 7,
            "Alamo Square": 11,
            "Richmond District": 20,
            "Financial District": 15,
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Marina District": 19,
            "Haight-Ashbury": 12,
            "Pacific Heights": 16,
            "Golden Gate Park": 17
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Alamo Square": 10,
            "Richmond District": 12,
            "Financial District": 13,
            "Union Square": 12,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Haight-Ashbury": 11,
            "Mission District": 15,
            "Golden Gate Park": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Alamo Square": 9,
            "Richmond District": 7,
            "Financial District": 26,
            "Union Square": 22,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Pacific Heights": 16
        }
    }

    friends = [
        {'name': 'William', 'location': 'Alamo Square', 'start': 915, 'end': 1035, 'duration': 60},
        {'name': 'Joshua', 'location': 'Richmond District', 'start': 420, 'end': 1200, 'duration': 15},
        {'name': 'Joseph', 'location': 'Financial District', 'start': 675, 'end': 810, 'duration': 15},
        {'name': 'David', 'location': 'Union Square', 'start': 1005, 'end': 1155, 'duration': 45},
        {'name': 'Brian', 'location': "Fisherman's Wharf", 'start': 825, 'end': 1245, 'duration': 105},
        {'name': 'Karen', 'location': 'Marina District', 'start': 690, 'end': 1110, 'duration': 15},
        {'name': 'Anthony', 'location': 'Haight-Ashbury', 'start': 435, 'end': 630, 'duration': 30},
        {'name': 'Matthew', 'location': 'Mission District', 'start': 1035, 'end': 1155, 'duration': 120},
        {'name': 'Helen', 'location': 'Pacific Heights', 'start': 480, 'end': 720, 'duration': 75},
        {'name': 'Jeffrey', 'location': 'Golden Gate Park', 'start': 1140, 'end': 1290, 'duration': 60}
    ]

    best_schedule = None
    best_count = -1

    for perm in itertools.permutations(friends):
        current_location = "The Castro"
        current_time = 540
        schedule = []
        for friend in perm:
            if current_location in travel_matrix and friend['location'] in travel_matrix[current_location]:
                travel_time = travel_matrix[current_location][friend['location']]
                arrive_time = current_time + travel_time
                start_time = max(arrive_time, friend['start'])
                end_time = start_time + friend['duration']
                if end_time <= friend['end']:
                    schedule.append({
                        'friend': friend,
                        'start_time': start_time,
                        'end_time': end_time
                    })
                    current_location = friend['location']
                    current_time = end_time
        if len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule
        if best_count == 10:
            break

    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    itinerary = []
    if best_schedule is not None:
        for meeting in best_schedule:
            f = meeting['friend']
            itinerary.append({
                "action": "meet",
                "location": f['location'],
                "person": f['name'],
                "start_time": format_time(meeting['start_time']),
                "end_time": format_time(meeting['end_time'])
            })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()