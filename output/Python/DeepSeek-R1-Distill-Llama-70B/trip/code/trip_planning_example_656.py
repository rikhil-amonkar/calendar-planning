import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Reykjavik': 5,
            'Istanbul': 4,
            'Edinburgh': 5,
            'Oslo': 2,
            'Stuttgart': 3,
            'Bucharest': 5
        }
        self.direct_flights = {
            'Bucharest': ['Oslo', 'Istanbul'],
            'Istanbul': ['Oslo', 'Edinburgh', 'Stuttgart'],
            'Edinburgh': ['Stuttgart'],
            'Oslo': ['Reykjavik'],
            'Stuttgart': ['Reykjavik'],
            'Reykjavik': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Bucharest
        self.add_place('Bucharest', 5)
        # Fly to Istanbul
        self.add_flight('Bucharest', 'Istanbul')
        self.add_place('Istanbul', 4)
        # Fly to Edinburgh
        self.add_flight('Istanbul', 'Edinburgh')
        self.add_place('Edinburgh', 5)
        # Fly to Stuttgart
        self.add_flight('Edinburgh', 'Stuttgart')
        self.add_place('Stuttgart', 3)
        # Fly to Reykjavik
        self.add_flight('Stuttgart', 'Reykjavik')
        self.add_place('Reykjavik', 5)
        # Fly to Oslo
        self.add_flight('Reykjavik', 'Oslo')
        self.add_place('Oslo', 2)

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