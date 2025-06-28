import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Hamburg': 7,
            'Munich': 6,
            'Manchester': 2,
            'Lyon': 2,
            'Split': 7
        }
        self.flights = {
            ('Split', 'Munich'): 2,
            ('Munich', 'Manchester'): 2,
            ('Hamburg', 'Manchester'): 2,
            ('Hamburg', 'Munich'): 2,
            ('Split', 'Lyon'): 2,
            ('Lyon', 'Munich'): 2,
            ('Hamburg', 'Split'): 2,
            ('Manchester', 'Split'): 2
        }
        self.itinerary = []
        self.current_day = 1
        self.visited_cities = set()

    def plan_trip(self):
        # Start in Hamburg
        self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.cities['Hamburg'] - 1}", "place": "Hamburg"})
        self.current_day += self.cities['Hamburg']
        self.visited_cities.add("Hamburg")

        # Visit other cities
        while self.current_day <= 20:
            # Get the next available city
            next_city = self.get_next_city()
            if next_city is None:
                break

            # Add the next city to the itinerary
            self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.cities[next_city] - 1}", "place": next_city})
            self.current_day += self.cities[next_city]
            self.visited_cities.add(next_city)

    def get_next_city(self):
        # Get the cities that have not been visited yet and can be reached from the current city
        available_cities = []
        for (city1, city2), duration in self.flights.items():
            if city1 in self.visited_cities and city2 not in self.visited_cities:
                available_cities.append((city2, duration))
            elif city2 in self.visited_cities and city1 not in self.visited_cities:
                available_cities.append((city1, duration))
        available_cities.sort(key=lambda x: x[1], reverse=True)

        # Return the city with the longest duration
        if available_cities:
            return available_cities[0][0]
        else:
            return None

    def output_json(self):
        return json.dumps({"itinerary": self.itinerary})

if __name__ == "__main__":
    planner = TripPlanner()
    planner.plan_trip()
    print(planner.output_json())