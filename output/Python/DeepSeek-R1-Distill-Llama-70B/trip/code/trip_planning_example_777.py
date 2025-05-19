import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Dublin': 5,
            'Helsinki': 3,
            'Riga': 3,
            'Reykjavik': 2,
            'Vienna': 2,
            'Tallinn': 5
        }
        self.direct_flights = {
            'Helsinki': ['Riga', 'Dublin', 'Tallinn'],
            'Riga': ['Tallinn', 'Dublin'],
            'Vienna': ['Helsinki', 'Riga', 'Dublin'],
            'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
            'Dublin': ['Tallinn'],
            'Tallinn': ['Dublin']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Vienna for the annual show
        self.add_place('Vienna', 2)
        # Fly to Helsinki to meet friends
        self.add_flight('Vienna', 'Helsinki')
        self.add_place('Helsinki', 3)
        # Fly to Riga
        self.add_flight('Helsinki', 'Riga')
        self.add_place('Riga', 3)
        # Fly to Reykjavik
        self.add_flight('Riga', 'Reykjavik')
        self.add_place('Reykjavik', 2)
        # Fly to Dublin
        self.add_flight('Reykjavik', 'Dublin')
        self.add_place('Dublin', 5)
        # Fly to Tallinn for the wedding
        self.add_flight('Dublin', 'Tallinn')
        self.add_place('Tallinn', 5)

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