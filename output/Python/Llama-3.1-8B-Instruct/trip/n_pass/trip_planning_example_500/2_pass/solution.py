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
            ('Split', 'Munich'): 1,
            ('Munich', 'Manchester'): 1,
            ('Hamburg', 'Manchester'): 1,
            ('Hamburg', 'Munich'): 1,
            ('Split', 'Lyon'): 1,
            ('Lyon', 'Munich'): 1,
            ('Hamburg', 'Split'): 1,
            ('Manchester', 'Split'): 1
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

    def output_json(self):
        return json.dumps({"itinerary": self.itinerary})

if __name__ == "__main__":
    planner = TripPlanner()
    planner.plan_trip()
    print(planner.output_json())