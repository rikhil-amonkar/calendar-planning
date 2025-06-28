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

    def plan_trip(self):
        # Start in Hamburg
        self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.cities['Hamburg'] - 1}", "place": "Hamburg"})
        self.current_day += self.cities['Hamburg']

        # Visit Munich
        if self.current_day + self.flights.get(('Hamburg', 'Munich'), 0) <= 20:
            self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.flights.get(('Hamburg', 'Munich'), 0)}", "place": "Munich"})
            self.current_day += self.flights.get(('Hamburg', 'Munich'), 0)

        # Visit Manchester
        if self.current_day + self.flights.get(('Munich', 'Manchester'), 0) <= 20:
            self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.flights.get(('Munich', 'Manchester'), 0)}", "place": "Manchester"})
            self.current_day += self.flights.get(('Munich', 'Manchester'), 0)

        # Visit Split
        if self.current_day + self.flights.get(('Manchester', 'Split'), 0) <= 20:
            self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.flights.get(('Manchester', 'Split'), 0)}", "place": "Split"})
            self.current_day += self.flights.get(('Manchester', 'Split'), 0)

        # Visit Lyon
        if self.current_day + self.flights.get(('Split', 'Lyon'), 0) <= 20:
            self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + self.flights.get(('Split', 'Lyon'), 0)}", "place": "Lyon"})
            self.current_day += self.flights.get(('Split', 'Lyon'), 0)

        # Ensure the itinerary covers exactly 20 days
        if self.current_day < 20:
            # If the itinerary is shorter than 20 days, add more cities
            for city, duration in self.cities.items():
                if city not in [itinerary["place"] for itinerary in self.itinerary]:
                    if self.current_day + duration <= 20:
                        self.itinerary.append({"day_range": f"Day {self.current_day}-{self.current_day + duration - 1}", "place": city})
                        self.current_day += duration

    def output_json(self):
        return json.dumps({"itinerary": self.itinerary})

if __name__ == "__main__":
    planner = TripPlanner()
    planner.plan_trip()
    print(planner.output_json())