import heapq
from datetime import datetime, timedelta

# Define travel times as a graph
travel_times = {
    'Mission District': {'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25, 'Marina District': 19, 'Pacific Heights': 16, 'Golden Gate Park': 17, 'Chinatown': 16, 'Richmond District': 20},
    'The Castro': {'Mission District': 7, 'Nob Hill': 16, 'Presidio': 20, 'Marina District': 21, 'Pacific Heights': 16, 'Golden Gate Park': 11, 'Chinatown': 22, 'Richmond District': 16},
    'Nob Hill': {'Mission District': 13, 'The Castro': 17, 'Presidio': 17, 'Marina District': 11, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Chinatown': 6, 'Richmond District': 14},
    'Presidio': {'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Marina District': 11, 'Pacific Heights': 11, 'Golden Gate Park': 12, 'Chinatown': 21, 'Richmond District': 7},
    'Marina District': {'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Chinatown': 15, 'Richmond District': 11},
    'Pacific Heights': {'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11, 'Marina District': 6, 'Golden Gate Park': 15, 'Chinatown': 11, 'Richmond District': 12},
    'Golden Gate Park': {'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11, 'Marina District': 16, 'Pacific Heights': 16, 'Chinatown': 23, 'Richmond District': 7},
    'Chinatown': {'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19, 'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23, 'Richmond District': 20},
    'Richmond District': {'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7, 'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Chinatown': 20}
}

# Define meeting constraints
meetings = {
    'Lisa': {'location': 'The Castro', 'start': 19 * 60 + 15, 'end': 21 * 60 + 15, 'duration': 120},
    'Daniel': {'location': 'Nob Hill', 'start': 8 * 60 + 15, 'end': 11 * 60, 'duration': 15},
    'Elizabeth': {'location': 'Presidio', 'start': 21 * 60 + 15, 'end': 22 * 60 + 15, 'duration': 45},
    'Steven': {'location': 'Marina District', 'start': 16 * 60 + 30, 'end': 20 * 60 + 45, 'duration': 90},
    'Timothy': {'location': 'Pacific Heights', 'start': 12 * 60, 'end': 18 * 60, 'duration': 90},
    'Ashley': {'location': 'Golden Gate Park', 'start': 20 * 60 + 45, 'end': 21 * 60 + 45, 'duration': 60},
    'Kevin': {'location': 'Chinatown', 'start': 12 * 60, 'end': 19 * 60, 'duration': 30},
    'Betty': {'location': 'Richmond District', 'start': 13 * 60 + 15, 'end': 15 * 60 + 45, 'duration': 30}
}

def time_to_str(minutes):
    return str(timedelta(minutes=minutes))[:-3]

def dijkstra(graph, start):
    distances = {node: float('inf') for node in graph}
    distances[start] = 0
    priority_queue = [(0, start)]
    previous_nodes = {node: None for node in graph}
    
    while priority_queue:
        current_distance, current_node = heapq.heappop(priority_queue)
        
        if current_distance > distances[current_node]:
            continue
        
        for neighbor, weight in graph[current_node].items():
            distance = current_distance + weight
            
            if distance < distances[neighbor]:
                distances[neighbor] = distance
                previous_nodes[neighbor] = current_node
                heapq.heappush(priority_queue, (distance, neighbor))
    
    return distances, previous_nodes

def get_path(previous_nodes, start, target):
    path = []
    while target != start:
        path.append(target)
        target = previous_nodes[target]
    path.append(start)
    return path[::-1]

def find_schedule():
    start_location = 'Mission District'
    start_time = 9 * 60
    current_time = start_time
    current_location = start_location
    visited = set()
    itinerary = []

    # Calculate shortest paths from start location
    distances, _ = dijkstra(travel_times, start_location)

    # Priority queue to explore meeting opportunities
    pq = []
    for person, details in meetings.items():
        if details['location'] == start_location and details['start'] >= current_time + details['duration']:
            heapq.heappush(pq, (details['start'], person))
        elif details['location'] != start_location:
            travel_time = distances[details['location']]
            if current_time + travel_time + details['duration'] <= details['end']:
                heapq.heappush(pq, (current_time + travel_time, person))

    while pq:
        next_meeting_time, person = heapq.heappop(pq)
        if person in visited:
            continue

        meeting_details = meetings[person]
        travel_time = distances[meeting_details['location']] if meeting_details['location'] != current_location else 0
        actual_start_time = max(current_time + travel_time, meeting_details['start'])
        actual_end_time = actual_start_time + meeting_details['duration']

        if actual_end_time <= meeting_details['end']:
            itinerary.append({
                "action": "meet",
                "location": meeting_details['location'],
                "person": person,
                "start_time": time_to_str(actual_start_time),
                "end_time": time_to_str(actual_end_time)
            })
            current_time = actual_end_time
            current_location = meeting_details['location']
            visited.add(person)

            # Re-evaluate remaining opportunities
            for other_person, other_details in meetings.items():
                if other_person not in visited:
                    travel_time = distances[other_details['location']] if other_details['location'] != current_location else 0
                    if current_time + travel_time + other_details['duration'] <= other_details['end']:
                        heapq.heappush(pq, (current_time + travel_time, other_person))

    return {"itinerary": itinerary}

# Generate and print the schedule
schedule = find_schedule()
print(schedule)