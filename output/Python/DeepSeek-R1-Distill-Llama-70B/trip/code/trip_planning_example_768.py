import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 4,
            'Nice': 3,
            'London': 2,
            'Copenhagen': 3,
            'Oslo': 5,
            'Tallinn': 4
        }
        self.direct_flights = {
            'Mykonos': ['London', 'Nice'],
            'London': ['Copenhagen', 'Nice', 'Oslo'],
            'Copenhagen': ['Tallinn', 'Nice', 'Oslo'],
            'Oslo': ['Nice'],
            'Nice': [],
            'Tallinn': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Mykonos
        self.add_place('Mykonos', 4)
        # Fly to London
        self.add_flight('Mykonos', 'London')
        self.add_place('London', 2)
        # Fly to Copenhagen
        self.add_flight('London', 'Copenhagen')
        self.add_place('Copenhagen', 3)
        # Fly to Oslo
        self.add_flight('Copenhagen', 'Oslo')
        self.add_place('Oslo', 5)
        # Fly to Nice for the conference
        self.add_flight('Oslo', 'Nice')
        self.add_place('Nice', 3)
        # Fly to Tallinn
        self.add_flight('Nice', 'Tallinn')
        self.add_place('Tallinn', 4)

    def add_place(self, place, days):
        end_day = self.current_day + days - 1
        self.itinerary.append({'day_range': f'Day {self.current_day}-{end_day}', 'place': place})
        self.current_day = end_day + 1

    def add_flight(self, from_city, to_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})
        self.current_day += 1

planner = TripPlanner()
planner.plan_trip()
print(json.dumps(planner.itinerary))