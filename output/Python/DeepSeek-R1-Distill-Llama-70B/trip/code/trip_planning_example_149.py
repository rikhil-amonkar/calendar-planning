import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'London': 3,
            'Santorini': 6,
            'Istanbul': 3
        }
        self.direct_flights = {
            'London': ['Santorini', 'Istanbul'],
            'Santorini': ['London'],
            'Istanbul': ['London']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with London
        self.add_place('London', 3)
        # Fly to Santorini
        self.add_flight('London', 'Santorini')
        self.add_place('Santorini', 6)
        # Fly back to London
        self.add_flight('Santorini', 'London')
        # Fly to Istanbul
        self.add_flight('London', 'Istanbul')
        self.add_place('Istanbul', 3)

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