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

    def plan_trip(self):
        # Start in Hamburg
        self.itinerary.append({"day_range": f"Day 1-{self.cities['Hamburg']}", "place": "Hamburg"})

        # Visit Munich
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg']}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0)}", "place": "Munich"})

        # Visit Manchester
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0)}", "place": "Manchester"})

        # Visit Split
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0)}", "place": "Split"})

        # Visit Lyon
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0)}", "place": "Lyon"})

        # Visit Manchester again
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0)}", "place": "Manchester"})

        # Visit relatives in Manchester
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0)}", "place": "Manchester"})

        # Visit relatives in Manchester again
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0)}", "place": "Manchester"})

        # Visit Split again
        if self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Manchester', 'Split'), 0) > 20:
            return
        self.itinerary.append({"day_range": f"Day {self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0)}-{self.cities['Hamburg'] + self.flights.get(('Hamburg', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Split', 'Lyon'), 0) + self.flights.get(('Lyon', 'Munich'), 0) + self.flights.get(('Munich', 'Manchester'), 0) + self.flights.get(('Manchester', 'Split'), 0) + self.flights.get(('Manchester', 'Split'), 0)}", "place": "Split"})

    def output_json(self):
        return json.dumps({"itinerary": self.itinerary})

if __name__ == "__main__":
    planner = TripPlanner()
    planner.plan_trip()
    print(planner.output_json())