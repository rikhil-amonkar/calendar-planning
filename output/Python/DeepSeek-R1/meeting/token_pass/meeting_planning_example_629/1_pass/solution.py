import itertools
import json

def main():
    # Travel time matrix (directed graph)
    travel_time = {
        'Russian Hill': {
            'Presidio': 14,
            'Chinatown': 9,
            'Pacific Heights': 7,
            'Richmond District': 14,
            'Fisherman\'s Wharf': 7,
            'Golden Gate Park': 21,
            'Bayview': 23
        },
        'Presidio': {
            'Russian Hill': 14,
            'Chinatown': 21,
            'Pacific Heights': 11,
            'Richmond District': 7,
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Bayview': 31
        },
        'Chinatown': {
            'Russian Hill': 7,
            'Presidio': 19,
            'Pacific Heights': 10,
            'Richmond District': 20,
            'Fisherman\'s Wharf': 8,
            'Golden Gate Park': 23,
            'Bayview': 22
        },
        'Pacific Heights': {
            'Russian Hill': 7,
            'Presidio': 11,
            'Chinatown': 11,
            'Richmond District': 12,
            'Fisherman\'s Wharf': 13,
            'Golden Gate Park': 15,
            'Bayview': 22
        },
        'Richmond District': {
            'Russian Hill': 13,
            'Presidio': 7,
            'Chinatown': 20,
            'Pacific Heights': 10,
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Bayview': 26
        },
        'Fisherman\'s Wharf': {
            'Russian Hill': 7,
            'Presidio': 17,
            'Chinatown': 12,
            'Pacific Heights': 12,
            'Richmond District': 18,
            'Golden Gate Park': 25,
            'Bayview': 26
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Presidio': 11,
            'Chinatown': 23,
            'Pacific Heights': 16,
            'Richmond District': 7,
            'Fisherman\'s Wharf': 24,
            'Bayview': 23
        },
        'Bayview': {
            'Russian Hill': 23,
            'Presidio': 31,
            'Chinatown': 18,
            'Pacific Heights': 23,
            'Richmond District': 25,
            'Fisherman\'s Wharf': 25,
            'Golden Gate Park': 22
        }
    }

    class Friend:
        def __init__(self, name, location, start_avail, end_avail, min_duration):
            self.name = name
            self.location = location
            self.start_avail = start_avail
            self.end_avail = end_avail
            self.min_duration = min_duration

    # Convert time to minutes from midnight
    friends = [
        Friend('Matthew', 'Presidio', 11*60, 21*60, 90),
        Friend('Margaret', 'Chinatown', 9*60+15, 18*60+45, 90),
        Friend('Nancy', 'Pacific Heights', 14*60+15, 17*60, 15),
        Friend('Helen', 'Richmond District', 19*60+45, 22*60, 60),
        Friend('Rebecca', 'Fisherman\'s Wharf', 21*60+15, 22*60+15, 60),
        Friend('Kimberly', 'Golden Gate Park', 13*60, 16*60+30, 120),
        Friend('Kenneth', 'Bayview', 14*60+30, 18*60, 60)
    ]

    start_time = 9*60  # 9:00 AM in minutes from midnight
    start_location = 'Russian Hill'
    best_schedule = None
    best_count = 0

    for order in itertools.permutations(friends):
        current_time = start_time
        current_loc = start_location
        schedule = []
        count = 0
        for friend in order:
            tt = travel_time[current_loc][friend.location]
            current_time += tt
            if current_time < friend.start_avail:
                current_time = friend.start_avail
            if current_time + friend.min_duration > friend.end_avail:
                break
            end_time = current_time + friend.min_duration
            schedule.append((current_time, end_time, friend.name, friend.location))
            current_time = end_time
            current_loc = friend.location
            count += 1

        if count > best_count:
            best_count = count
            best_schedule = schedule
            if count == len(friends):
                break

    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            start_minutes = meeting[0]
            end_minutes = meeting[1]
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "location": meeting[3],
                "person": meeting[2],
                "start_time": start_str,
                "end_time": end_str
            })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()