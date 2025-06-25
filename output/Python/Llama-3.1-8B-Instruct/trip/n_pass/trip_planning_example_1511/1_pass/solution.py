import json
from collections import defaultdict

class TripPlanner:
    def __init__(self, cities, durations, transitions):
        self.cities = cities
        self.durations = durations
        self.transitions = transitions

    def compute_itinerary(self):
        # Initialize the graph with all cities
        graph = defaultdict(list)
        for transition in self.transitions:
            graph[transition[0]].append(transition[1])

        # Initialize the current city and day
        current_city = 'Bucharest'
        current_day = 1
        itinerary = []

        # Initialize the visited cities
        visited_cities = set()

        # Function to add a city to the itinerary
        def add_city(city, day_range):
            if city not in visited_cities:
                visited_cities.add(city)
                itinerary.append({"day_range": f"Day {current_day}-{current_day + day_range - 1}", "place": city})
                current_day += day_range

        # Visit each city
        for city, duration in self.durations.items():
            if city == 'Venice':
                add_city(city, 3)
                add_city(city, 3)
            elif city == 'Reykjavik':
                add_city(city, 2)
            elif city == 'Munich':
                add_city(city, 3)
                if current_day >= 4 and current_day <= 6:
                    add_city(city, 3)
            elif city == 'Santorini':
                add_city(city, 3)
                add_city(city, 3)
            elif city == 'Manchester':
                add_city(city, 3)
            elif city == 'Porto':
                add_city(city, 3)
            elif city == 'Bucharest':
                add_city(city, 5)
            elif city == 'Tallinn':
                add_city(city, 4)
            elif city == 'Valencia':
                add_city(city, 2)
                if current_day >= 14 and current_day <= 15:
                    add_city(city, 2)
            elif city == 'Vienna':
                add_city(city, 5)

            # Move to the next city
            if city in graph:
                next_city = graph[city][0]
                if next_city not in visited_cities:
                    current_city = next_city

        return itinerary

    def run(self):
        itinerary = self.compute_itinerary()
        return {"itinerary": itinerary}

def main():
    cities = ['Bucharest', 'Manchester', 'Munich', 'Santorini', 'Reykjavik', 'Porto', 'Vienna', 'Valencia', 'Tallinn', 'Venice']
    durations = {
        'Bucharest': 5,
        'Manchester': 3,
        'Munich': 6,
        'Santorini': 6,
        'Reykjavik': 2,
        'Porto': 3,
        'Vienna': 5,
        'Valencia': 4,
        'Tallinn': 4,
        'Venice': 6
    }
    transitions = [
        ('Bucharest', 'Manchester'),
        ('Manchester', 'Munich'),
        ('Munich', 'Venice'),
        ('Venice', 'Santorini'),
        ('Santorini', 'Manchester'),
        ('Manchester', 'Reykjavik'),
        ('Reykjavik', 'Porto'),
        ('Porto', 'Vienna'),
        ('Vienna', 'Valencia'),
        ('Valencia', 'Tallinn'),
        ('Tallinn', 'Munich'),
        ('Munich', 'Santorini'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Vienna'),
        ('Bucharest', 'Valencia'),
        ('Venice', 'Manchester'),
        ('Porto', 'Manchester'),
        ('Munich', 'Bucharest'),
        ('Santorini', 'Bucharest'),
        ('Munich', 'Valencia')
    ]

    planner = TripPlanner(cities, durations, transitions)
    result = planner.run()
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()