import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Oslo': 2,
            'Helsinki': 2,
            'Edinburgh': 3,
            'Riga': 2,
            'Tallinn': 5,
            'Budapest': 5,
            'Vilnius': 5,
            'Porto': 5,
            'Geneva': 4
        }
        self.direct_flights = {
            'Porto': ['Oslo'],
            'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Oslo', 'Helsinki', 'Riga'],
            'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
            'Tallinn': ['Vilnius', 'Helsinki', 'Oslo'],
            'Budapest': ['Geneva', 'Oslo'],
            'Vilnius': ['Helsinki', 'Oslo'],
            'Geneva': ['Porto', 'Oslo'],
            'Helsinki': ['Budapest', 'Oslo', 'Geneva'],
            'Oslo': []
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Edinburgh
        self.add_place('Edinburgh', 3)
        # Fly to Tallinn for the wedding
        self.add_flight('Edinburgh', 'Tallinn')
        self.add_place('Tallinn', 5)
        # Fly to Helsinki
        self.add_flight('Tallinn', 'Helsinki')
        self.add_place('Helsinki', 2)
        # Fly to Budapest
        self.add_flight('Helsinki', 'Budapest')
        self.add_place('Budapest', 5)
        # Fly to Geneva
        self.add_flight('Budapest', 'Geneva')
        self.add_place('Geneva', 4)
        # Fly to Porto
        self.add_flight('Geneva', 'Porto')
        self.add_place('Porto', 5)
        # Fly to Oslo to meet the friend
        self.add_flight('Porto', 'Oslo')
        self.add_place('Oslo', 2)
        # Fly to Riga
        self.add_flight('Oslo', 'Riga')
        self.add_place('Riga', 2)
        # Fly to Vilnius
        self.add_flight('Riga', 'Vilnius')
        self.add_place('Vilnius', 5)

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