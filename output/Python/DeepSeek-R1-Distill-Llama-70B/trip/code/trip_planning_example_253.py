import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Amsterdam': 3,
            'Vienna': 7,
            'Santorini': 4,
            'Lyon': 3
        }
        self.direct_flights = {
            'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
            'Amsterdam': ['Santorini'],
            'Lyon': ['Vienna', 'Amsterdam'],
            'Santorini': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Lyon for the wedding
        self.add_place('Lyon', 3)
        # Fly to Vienna
        self.add_flight('Lyon', 'Vienna')
        self.add_place('Vienna', 7)
        # Fly to Amsterdam for the workshop
        self.add_flight('Vienna', 'Amsterdam')
        self.add_place('Amsterdam', 3)
        # Fly to Santorini
        self.add_flight('Amsterdam', 'Santorini')
        self.add_place('Santorini', 4)

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