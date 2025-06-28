import json
from collections import deque

class TripPlanner:
    def __init__(self):
        self.cities = {
            "Oslo": 5,
            "Stuttgart": 5,
            "Reykjavik": 2,
            "Split": 3,
            "Geneva": 2,
            "Porto": 3,
            "Tallinn": 5,
            "Stockholm": 3
        }
        self.flights = {
            "Reykjavik": ["Stuttgart", "Stockholm", "Oslo"],
            "Stockholm": ["Oslo", "Tallinn", "Stuttgart", "Split", "Geneva"],
            "Oslo": ["Reykjavik", "Split", "Geneva", "Porto"],
            "Stuttgart": ["Reykjavik", "Porto", "Split"],
            "Split": ["Oslo", "Stuttgart", "Stockholm", "Geneva"],
            "Geneva": ["Stockholm", "Split", "Porto"],
            "Porto": ["Stuttgart", "Oslo", "Geneva"],
            "Tallinn": ["Reykjavik", "Oslo", "Stockholm"]
        }

    def calculate_itinerary(self):
        # Create a graph from the flights
        graph = {city: neighbors for city, neighbors in self.flights.items()}

        # Initialize the queue with the starting city
        queue = deque([(list(self.cities.keys())[0], 1, 0, [list(self.cities.keys())[0]])])

        # Initialize the result
        result = []

        while queue:
            city, day, total_days, path = queue.popleft()

            # If we've visited all cities, return the result
            if total_days >= 21:
                result.append({"day_range": f"Day {day}-{day + self.cities[city] - 1}", "place": city})
                continue

            # Add the current city to the result
            result.append({"day_range": f"Day {day}-{day + self.cities[city] - 1}", "place": city})

            # Add the neighbors of the current city to the queue
            for neighbor in graph[city]:
                if neighbor not in path:
                    queue.append((neighbor, day + 1, total_days + self.cities[city], path + [neighbor]))

        return {"itinerary": result}

def main():
    trip_planner = TripPlanner()
    result = trip_planner.calculate_itinerary()
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()