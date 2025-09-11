import copy
import json

# Define locations and distance matrix
distance_matrix = [
    [0, 16, 17, 9, 10, 10, 20, 20, 13, 13, 27],  # Richmond District
    [16, 0, 16, 21, 16, 6, 7, 22, 18, 8, 19],    # The Castro
    [14, 17, 0, 11, 8, 13, 13, 6, 5, 11, 19],    # Nob Hill
    [11, 22, 12, 0, 7, 16, 20, 15, 8, 15, 27],   # Marina District
    [12, 16, 8, 6, 0, 11, 15, 11, 7, 10, 22],    # Pacific Heights
    [10, 6, 15, 17, 12, 0, 11, 19, 17, 5, 18],   # Haight-Ashbury
    [20, 7, 12, 19, 16, 12, 0, 16, 15, 11, 14],  # Mission District
    [20, 22, 9, 12, 10, 19, 17, 0, 7, 17, 20],   # Chinatown
    [14, 21, 5, 7, 7, 17, 16, 9, 0, 13, 23],     # Russian Hill
    [11, 8, 11, 15, 10, 5, 10, 15, 13, 0, 16],   # Alamo Square
    [25, 19, 20, 27, 23, 19, 13, 19, 23, 16, 0], # Bayview
]

friends = [
    {
        'name': 'Matthew',
        'location_idx': 1,
        'available_from': 990,
        'available_to': 1200,
        'required_duration': 45,
    },
    {
        'name': 'Rebecca',
        'location_idx': 2,
        'available_from': 915,
        'available_to': 1155,
        'required_duration': 105,
    },
    {
        'name': 'Brian',
        'location_idx': 3,
        'available_from': 855,
        'available_to': 1320,
        'required_duration': 30,
    },
    {
        'name': 'Emily',
        'location_idx': 4,
        'available_from': 675,
        'available_to': 1185,
        'required_duration': 15,
    },
    {
        'name': 'Karen',
        'location_idx': 5,
        'available_from': 705,
        'available_to': 1050,
        'required_duration': 30,
    },
    {
        'name': 'Stephanie',
        'location_idx': 6,
        'available_from': 780,
        'available_to': 945,
        'required_duration': 75,
    },
    {
        'name': 'James',
        'location_idx': 7,
        'available_from': 870,
        'available_to': 1140,
        'required_duration': 120,
    },
    {
        'name': 'Steven',
        'location_idx': 8,
        'available_from': 840,
        'available_to': 1200,
        'required_duration': 30,
    },
    {
        'name': 'Elizabeth',
        'location_idx': 9,
        'available_from': 780,
        'available_to': 1035,
        'required_duration': 120,
    },
    {
        'name': 'William',
        'location_idx': 10,
        'available_from': 1095,
        'available_to': 1215,
        'required_duration': 90,
    },
]

best_itinerary = []

def backtrack(current_time, current_location, visited, itinerary):
    global best_itinerary

    # Update best itinerary if current is better
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary.copy()

    # Try all friends not yet visited
    for i in range(len(friends)):
        if i not in visited:
            friend = friends[i]
            # Calculate travel time
            travel_time = distance_matrix[current_location][friend['location_idx']]
            arrival_time = current_time + travel_time

            # Determine earliest possible start time for meeting
            start_meeting = max(arrival_time, friend['available_from'])
            end_meeting = start_meeting + friend['required_duration']

            # Check if meeting can be accommodated within friend's available time
            if end_meeting <= friend['available_to']:
                # Add this friend to the itinerary
                visited.add(i)
                itinerary.append({
                    'name': friend['name'],
                    'location': friend['location_idx'],
                    'start_time': start_meeting,
                    'end_time': end_meeting,
                })
                # Recurse
                backtrack(end_meeting, friend['location_idx'], visited, itinerary)
                # Backtrack
                itinerary.pop()
                visited.remove(i)

# Initial call: starting at Richmond District (location 0) at 9:00 AM (540 mins)
initial_time = 9 * 60  # 540
initial_location = 0
backtrack(initial_time, initial_location, set(), [])

# Convert best_itinerary to the required JSON format
def to_json(itinerary):
    result = {
        "itinerary": []
    }
    for meet in itinerary:
        start_time = f"{meet['start_time'] // 60}:{meet['start_time'] % 60:02d}"
        end_time = f"{meet['end_time'] // 60}:{meet['end_time'] % 60:02d}"
        location_name = {
            1: 'The Castro',
            2: 'Nob Hill',
            3: 'Marina District',
            4: 'Pacific Heights',
            5: 'Haight-Ashbury',
            6: 'Mission District',
            7: 'Chinatown',
            8: 'Russian Hill',
            9: 'Alamo Square',
            10: 'Bayview',
        }[meet['location']]
        result["itinerary"].append({
            "action": "meet",
            "location": location_name,
            "person": meet['name'],
            "start_time": start_time,
            "end_time": end_time,
        })
    return result

print(json.dumps(to_json(best_itinerary), indent=2))