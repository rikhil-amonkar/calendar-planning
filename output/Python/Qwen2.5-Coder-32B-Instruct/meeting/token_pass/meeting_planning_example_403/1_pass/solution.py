import heapq
from datetime import datetime, timedelta
import json

# Define the travel times as a graph
travel_times = {
    'Union Square': {'Golden Gate Park': 22, 'Pacific Heights': 15, 'Presidio': 24, 'Chinatown': 7, 'The Castro': 19},
    'Golden Gate Park': {'Union Square': 22, 'Pacific Heights': 16, 'Presidio': 11, 'Chinatown': 23, 'The Castro': 13},
    'Pacific Heights': {'Union Square': 12, 'Golden Gate Park': 15, 'Presidio': 11, 'Chinatown': 11, 'The Castro': 16},
    'Presidio': {'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 'Chinatown': 21, 'The Castro': 21},
    'Chinatown': {'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 11, 'Presidio': 19, 'The Castro': 22},
    'The Castro': {'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 'Presidio': 20, 'Chinatown': 20}
}

# Define the meetings and their constraints
meetings = {
    'Andrew': {'location': 'Golden Gate Park', 'start': '11:45', 'end': '14:30', 'duration': 75},
    'Sarah': {'location': 'Pacific Heights', 'start': '16:15', 'end': '18:45', 'duration': 15},
    'Nancy': {'location': 'Presidio', 'start': '17:30', 'end': '19:15', 'duration': 60},
    'Rebecca': {'location': 'Chinatown', 'start': '09:45', 'end': '21:30', 'duration': 90},
    'Robert': {'location': 'The Castro', 'start': '08:30', 'end': '14:15', 'duration': 30}
}

# Function to convert time string to datetime object
def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Dijkstra's algorithm to find the shortest path between two locations
def dijkstra(graph, start, end):
    queue = [(0, start)]
    distances = {node: float('inf') for node in graph}
    distances[start] = 0
    previous_nodes = {node: None for node in graph}
    
    while queue:
        current_distance, current_node = heapq.heappop(queue)
        
        if current_distance > distances[current_node]:
            continue
        
        for neighbor, weight in graph[current_node].items():
            distance = current_distance + weight
            
            if distance < distances[neighbor]:
                distances[neighbor] = distance
                previous_nodes[neighbor] = current_node
                heapq.heappush(queue, (distance, neighbor))
    
    path, current_node = [], end
    while previous_nodes[current_node] is not None:
        path.append(current_node)
        current_node = previous_nodes[current_node]
    path.append(start)
    return path[::-1], distances[end]

# Main function to generate the itinerary
def generate_itinerary(meetings, travel_times):
    current_location = 'Union Square'
    current_time = parse_time('09:00')
    itinerary = []
    
    # Sort meetings by start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))
    
    for person, details in sorted_meetings:
        meeting_start = parse_time(details['start'])
        meeting_end = parse_time(details['end'])
        required_duration = timedelta(minutes=details['duration'])
        location = details['location']
        
        # Calculate travel time to the meeting location
        path, travel_time = dijkstra(travel_times, current_location, location)
        travel_duration = timedelta(minutes=travel_time)
        
        # Check if we can reach the meeting on time
        potential_start_time = current_time + travel_duration
        if potential_start_time >= meeting_start:
            # We can only start the meeting at the latest possible time
            actual_start_time = max(potential_start_time, meeting_start)
            actual_end_time = actual_start_time + required_duration
            
            # Check if the meeting fits within the friend's availability
            if actual_end_time <= meeting_end:
                # Add the meeting to the itinerary
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": actual_start_time.strftime('%H:%M'),
                    "end_time": actual_end_time.strftime('%H:%M')
                })
                
                # Update the current time and location
                current_time = actual_end_time
                current_location = location
    
    return {"itinerary": itinerary}

# Generate and print the itinerary
itinerary = generate_itinerary(meetings, travel_times)
print(json.dumps(itinerary, indent=2))