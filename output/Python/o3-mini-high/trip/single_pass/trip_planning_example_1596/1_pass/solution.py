#!/usr/bin/env python3
import json

def build_graph():
    edges = [
        ("Budapest", "Munich"),
        ("Bucharest", "Riga"),
        ("Munich", "Krakow"),
        ("Munich", "Warsaw"),
        ("Munich", "Bucharest"),
        ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"),
        ("Edinburgh", "Krakow"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"),
        ("Budapest", "Vienna"),
        ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"),
        ("Edinburgh", "Budapest"),
        ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"),
        ("Vienna", "Riga"),
        ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"),
        ("Vienna", "Krakow"),
        ("Edinburgh", "Munich"),
        ("Barcelona", "Bucharest"),
        ("Edinburgh", "Riga"),
        ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"),
        ("Barcelona", "Krakow"),
        ("Riga", "Munich"),
        ("Vienna", "Bucharest"),
        ("Budapest", "Warsaw"),
        ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"),
        ("Budapest", "Bucharest"),
        ("Vienna", "Munich"),
        ("Riga", "Warsaw"),
        ("Stockholm", "Riga"),
        ("Stockholm", "Warsaw")
    ]
    graph = {}
    for a, b in edges:
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    return graph

# Required durations for each city (in days)
durations = {
    "Edinburgh": 5,
    "Bucharest": 2,
    "Krakow": 4,
    "Munich": 3,
    "Barcelona": 5,
    "Warsaw": 5,
    "Budapest": 5,
    "Stockholm": 2,
    "Riga": 5,
    "Vienna": 5
}

# Event constraints: key is city, value is (event_start, event_end)
# The visit block for that city must overlap with the event window.
event_constraints = {
    "Edinburgh": (1, 5),     # Meet friend in Edinburgh between Day 1-5.
    "Budapest":   (9, 13),   # Annual show in Budapest between Day 9-13.
    "Munich":     (18, 20),  # Workshop in Munich between Day 18-20.
    "Stockholm":  (17, 18),  # Meet friends in Stockholm between Day 17-18.
    "Warsaw":     (25, 29)   # Conference in Warsaw between Day 25-29.
}

all_cities = set(durations.keys())

def compute_schedule(path):
    schedule = []
    current_day = 1
    for city in path:
        start = current_day
        end = start + durations[city] - 1
        schedule.append((city, start, end))
        # If flying on the same day, the landing day is the same as the previous city's end.
        current_day = end
    return schedule

def check_event_constraints(schedule):
    # For each city with an event, check that its scheduled stay overlaps the event window.
    for city, start, end in schedule:
        if city in event_constraints:
            event_start, event_end = event_constraints[city]
            # Check if there is any overlap between [start, end] and [event_start, event_end]
            if max(start, event_start) > min(end, event_end):
                return False
    return True

def backtrack(graph, current, path, visited):
    if len(path) == len(durations):
        schedule = compute_schedule(path)
        # The overall itinerary must cover 32 days.
        if schedule[-1][2] != 32:
            return None
        if check_event_constraints(schedule):
            return path
        return None
    for neighbor in graph.get(current, []):
        if neighbor not in visited:
            new_path = path + [neighbor]
            visited.add(neighbor)
            result = backtrack(graph, neighbor, new_path, visited)
            if result is not None:
                return result
            visited.remove(neighbor)
    return None

def main():
    graph = build_graph()
    # Fix the starting city to Edinburgh to satisfy the Edinburgh friend meeting constraint.
    start_city = "Edinburgh"
    path = [start_city]
    visited = {start_city}
    itinerary_path = backtrack(graph, start_city, path, visited)
    if itinerary_path is None:
        result = {"itinerary": []}
    else:
        schedule = compute_schedule(itinerary_path)
        itinerary_list = []
        for city, start, end in schedule:
            day_range = "Day {}-{}".format(start, end)
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()