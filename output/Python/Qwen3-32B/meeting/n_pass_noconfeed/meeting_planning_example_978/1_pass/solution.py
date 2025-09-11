import heapq
import json

def main():
    friends = [
        {
            'name': 'Joseph',
            'location': 'Presidio',
            'available_start': 7 * 60,  # 7:00 AM
            'available_end': 13 * 60,   # 1:00 PM
            'required': 45,
        },
        {
            'name': 'Joshua',
            'location': 'Haight-Ashbury',
            'available_start': 9 * 60,  # 9:00 AM
            'available_end': 15 * 60 + 30,  # 3:30 PM
            'required': 15,
        },
        {
            'name': 'Betty',
            'location': 'Marina District',
            'available_start': 10 * 60 + 45,  # 10:45 AM
            'available_end': 14 * 60 + 15,    # 2:15 PM
            'required': 60,
        },
        {
            'name': 'Lisa',
            'location': 'Financial District',
            'available_start': 10 * 60 + 45,  # 10:45 AM
            'available_end': 17 * 60 + 15,    # 5:15 PM
            'required': 15,
        },
        {
            'name': 'John',
            'location': 'The Castro',
            'available_start': 13 * 60 + 15,  # 1:15 PM
            'available_end': 19 * 60 + 45,    # 7:45 PM
            'required': 45,
        },
        {
            'name': 'Melissa',
            'location': 'Russian Hill',
            'available_start': 17 * 60,       # 5:00 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'required': 120,
        },
        {
            'name': 'Sarah',
            'location': 'Richmond District',
            'available_start': 16 * 60 + 15,  # 4:15 PM
            'available_end': 19 * 60 + 30,    # 7:30 PM
            'required': 105,
        },
        {
            'name': 'Daniel',
            'location': 'Pacific Heights',
            'available_start': 18 * 60 + 30,  # 6:30 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'required': 60,
        },
        {
            'name': 'Andrew',
            'location': 'Nob Hill',
            'available_start': 19 * 60 + 45,  # 7:45 PM
            'available_end': 22 * 60,         # 10:00 PM
            'required': 105,
        },
        {
            'name': 'Stephanie',
            'location': 'Fisherman\'s Wharf',
            'available_start': 15 * 60 + 30,  # 3:30 PM
            'available_end': 22 * 60,         # 10:00 PM
            'required': 30,
        },
    ]

    travel_times = {
        'Embarcadero': {
            'Fisherman\'s Wharf': 6,
            'Financial District': 5,
            'Russian Hill': 8,
            'Marina District': 12,
            'Richmond District': 21,
            'Pacific Heights': 11,
            'Haight-Ashbury': 21,
            'Presidio': 20,
            'Nob Hill': 10,
            'The Castro': 25,
        },
        'Fisherman\'s Wharf': {
            'Embarcadero': 8,
            'Financial District': 11,
            'Russian Hill': 7,
            'Marina District': 9,
            'Richmond District': 18,
            'Pacific Heights': 12,
            'Haight-Ashbury': 22,
            'Presidio': 17,
            'Nob Hill': 11,
            'The Castro': 27,
        },
        'Financial District': {
            'Embarcadero': 4,
            'Fisherman\'s Wharf': 10,
            'Russian Hill': 11,
            'Marina District': 15,
            'Richmond District': 21,
            'Pacific Heights': 13,
            'Haight-Ashbury': 19,
            'Presidio': 22,
            'Nob Hill': 8,
            'The Castro': 20,
        },
        'Russian Hill': {
            'Embarcadero': 8,
            'Fisherman\'s Wharf': 7,
            'Financial District': 11,
            'Marina District': 7,
            'Richmond District': 14,
            'Pacific Heights': 7,
            'Haight-Ashbury': 17,
            'Presidio': 14,
            'Nob Hill': 5,
            'The Castro': 21,
        },
        'Marina District': {
            'Embarcadero': 14,
            'Fisherman\'s Wharf': 10,
            'Financial District': 17,
            'Russian Hill': 8,
            'Richmond District': 11,
            'Pacific Heights': 7,
            'Haight-Ashbury': 16,
            'Presidio': 10,
            'Nob Hill': 12,
            'The Castro': 22,
        },
        'Richmond District': {
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 18,
            'Financial District': 22,
            'Russian Hill': 13,
            'Marina District': 9,
            'Pacific Heights': 10,
            'Haight-Ashbury': 10,
            'Presidio': 7,
            'Nob Hill': 17,
            'The Castro': 16,
        },
        'Pacific Heights': {
            'Embarcadero': 10,
            'Fisherman\'s Wharf': 13,
            'Financial District': 13,
            'Russian Hill': 7,
            'Marina District': 6,
            'Richmond District': 12,
            'Haight-Ashbury': 11,
            'Presidio': 11,
            'Nob Hill': 8,
            'The Castro': 16,
        },
        'Haight-Ashbury': {
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 23,
            'Financial District': 21,
            'Russian Hill': 17,
            'Marina District': 17,
            'Richmond District': 10,
            'Pacific Heights': 12,
            'Presidio': 15,
            'Nob Hill': 15,
            'The Castro': 6,
        },
        'Presidio': {
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 19,
            'Financial District': 23,
            'Russian Hill': 14,
            'Marina District': 11,
            'Richmond District': 7,
            'Pacific Heights': 11,
            'Haight-Ashbury': 15,
            'Nob Hill': 18,
            'The Castro': 21,
        },
        'Nob Hill': {
            'Embarcadero': 9,
            'Fisherman\'s Wharf': 10,
            'Financial District': 9,
            'Russian Hill': 5,
            'Marina District': 11,
            'Richmond District': 14,
            'Pacific Heights': 8,
            'Haight-Ashbury': 13,
            'Presidio': 17,
            'The Castro': 17,
        },
        'The Castro': {
            'Embarcadero': 22,
            'Fisherman\'s Wharf': 24,
            'Financial District': 21,
            'Russian Hill': 18,
            'Marina District': 21,
            'Richmond District': 16,
            'Pacific Heights': 16,
            'Haight-Ashbury': 6,
            'Presidio': 20,
            'Nob Hill': 16,
        },
    }

    num_friends = len(friends)

    best = {}
    heap = []
    initial_time = 9 * 60
    initial_location = 'Embarcadero'
    initial_bitmask = 0
    heapq.heappush(heap, (0, initial_time, initial_location, initial_bitmask, []))
    best_key = (initial_location, initial_bitmask)
    best[best_key] = initial_time

    max_visited = 0
    best_itinerary = []

    while heap:
        neg_num_visited, current_time, current_location, bitmask, path = heapq.heappop(heap)
        num_visited = -neg_num_visited

        if num_visited > max_visited:
            max_visited = num_visited
            best_itinerary = path.copy()

        current_key = (current_location, bitmask)
        if best.get(current_key, float('inf')) < current_time:
            continue

        for idx in range(num_friends):
            if not (bitmask & (1 << idx)):
                friend = friends[idx]
                friend_loc = friend['location']
                available_start = friend['available_start']
                available_end = friend['available_end']
                required = friend['required']

                if current_location not in travel_times or friend_loc not in travel_times[current_location]:
                    continue
                travel_time = travel_times[current_location][friend_loc]
                earliest_arrival = current_time + travel_time

                proposed_start = max(earliest_arrival, available_start)
                if proposed_start + required > available_end:
                    continue

                new_time = proposed_start + required
                new_location = friend_loc
                new_bitmask = bitmask | (1 << idx)
                new_path = path + [idx]

                new_key = (new_location, new_bitmask)
                if new_key not in best or new_time < best[new_key]:
                    best[new_key] = new_time
                    heapq.heappush(heap, (- (num_visited + 1), new_time, new_location, new_bitmask, new_path))

    def generate_itinerary(path, friends, travel_times):
        current_time = 9 * 60
        current_location = 'Embarcadero'
        result = []
        for idx in path:
            friend = friends[idx]
            friend_loc = friend['location']
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required']

            travel_time = travel_times[current_location][friend_loc]
            earliest_arrival = current_time + travel_time

            meeting_start = max(earliest_arrival, available_start)
            meeting_end = meeting_start + required

            result.append({
                'action': 'meet',
                'location': friend_loc,
                'person': friend['name'],
                'start_time': f"{meeting_start // 60}:{meeting_start % 60:02d}",
                'end_time': f"{meeting_end // 60}:{meeting_end % 60:02d}"
            })

            current_time = meeting_end
            current_location = friend_loc
        return result

    itinerary = generate_itinerary(best_itinerary, friends, travel_times)
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()