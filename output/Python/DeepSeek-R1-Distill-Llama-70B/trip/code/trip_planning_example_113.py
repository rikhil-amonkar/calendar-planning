import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Naples': 3,
            'Seville': 4,
            'Milan': 7
        }
        self.direct_flights = {
            'Milan': ['Seville'],
            'Seville': [],
            'Naples': ['Milan']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Naples
        self.add_place('Naples', 3)
        # Fly to Milan
        self.add_flight('Naples', 'Milan')
        self.add_place('Milan', 7)
        # Fly to Seville for the annual show
        self.add_flight('Milan', 'Seville')
        self.add_place('Seville', 4)

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