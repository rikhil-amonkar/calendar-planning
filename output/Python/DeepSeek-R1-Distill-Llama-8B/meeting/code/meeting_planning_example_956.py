import heapq

def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

# Read travel times
travel_times = {
    'The Castro': {
        'Alamo Square': 8,
        'Richmond District': 16,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman's Wharf': 24,
        'Marina District': 21,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 14,
        'Fisherman's Wharf': 19,
        'Marina District': 15,
        'Haight-Ashbury': 5,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Richmond District': {
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Fisherman's Wharf': 18,
        'Marina District': 9,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Financial District': {
        'The Castro': 20,
        'Alamo Square': 17,
        'Richmond District': 21,
        'Union Square': 9,
        'Fisherman's Wharf': 10,
        'Marina District': 15,
        'Haight-Ashbury': 19,
        'Mission District': 17,
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
    },
    'Union Square': {
        'The Castro': 17,
        'Alamo Square': 15,
        'Richmond District': 20,
        'Financial District': 9,
        'Fisherman's Wharf': 15,
        'Marina District': 18,
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
    },
    'Fisherman's Wharf': {
        'The Castro': 27,
        'Alamo Square': 21,
        'Richmond District': 18,
        'Financial District': 11,
        'Union Square': 13,
        'Marina District': 9,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
    },
    'Marina District': {
        'The Castro': 22,
        'Alamo Square': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 16,
        'Fisherman's Wharf': 10,
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Alamo Square': 5,
        'Richmond District': 10,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman's Wharf': 23,
        'Mission District': 11,
        'Pacific Heights': 12,
        'Golden Gate Park': 7,
    },
    'Mission District': {
        'The Castro': 7,
        'Alamo Square': 11,
        'Richmond District': 20,
        'Financial District': 15,
        'Union Square': 15,
        'Fisherman's Wharf': 22,
        'Marina District': 19,
        'Haight-Ashbury': 12,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Alamo Square': 10,
        'Richmond District': 12,
        'Financial District': 13,
        'Union Square': 12,
        'Fisherman's Wharf': 13,
        'Marina District': 6,
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Golden Gate Park': 15,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Alamo Square': 9,
        'Richmond District': 7,
        'Financial District': 26,
        'Union Square': 22,
        'Fisherman's Wharf': 24,
        'Marina District': 16,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Pacific Heights': 16,
    }
}

# Read people data and convert times to minutes
people = [
    {
        'name': 'William',
        'location': 'Alamo Square',
        'availability_start': '15:15',
        'availability_end': '17:15',
        'required_time': 60
    },
    {
        'name': 'Joshua',
        'location': 'Richmond District',
        'availability_start': '7:00',
        'availability_end': '20:00',
        'required_time': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'availability_start': '11:15',
        'availability_end': '13:30',
        'required_time': 15
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'availability_start': '16:45',
        'availability_end': '19:15',
        'required_time': 45
    },
    {
        'name': 'Brian',
        'location': 'Fisherman's Wharf',
        'availability_start': '14:45',
        'availability_end': '20:45',
        'required_time': 105
    },
    {
        'name': 'Karen',
        'location': 'Marina District',
        'availability_start': '11:30',
        'availability_end': '18:30',
        'required_time': 15
    },
    {
        'name': 'Anthony',
        'location': 'Haight-Ashbury',
        'availability_start': '7:15',
        'availability_end': '10:30',
        'required_time': 30
    },
    {
        'name': 'Matthew',
        'location': 'Mission District',
        'availability_start': '17:15',
        'availability_end': '19:15',
        'required_time': 120
    },
    {
        'name': 'Helen',
        'location': 'Pacific Heights',
        'availability_start': '8:00',
        'availability_end': '12:00',
        'required_time': 75
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'availability_start': '19:00',
        'availability_end': '21:30',
        'required_time': 60
    }
]

for person in people:
    person['availability_start'] = to_minutes(person['availability_start'])
    person['availability_end'] = to_minutes(person['availability_end'])

# Initialize priority queue
priority_queue = []

for person in people:
    from_loc = 'The Castro'
    to_loc = person['location']
    arrival_time = 540 + travel_times[from_loc][to_loc]
    avail_start = person['availability_start']
    avail_end = person['availability_end']
    required = person['required_time']
    
    earliest_start = max(arrival_time, avail_start)
    latest_start = avail_end - required
    
    if earliest_start <= latest_start:
        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, person))

schedule = []
current_end = 540  # 9:00 AM in minutes

while priority_queue:
    start_min, end_min, person = heapq.heappop(priority_queue)
    
    # Check if this meeting can be scheduled
    if start_min >= current_end:
        # Check if the meeting ends before the person's availability end
        if end_min <= person['availability_end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': format_time(start_min),
                'end_time': format_time(end_min)
            })
            current_end = end_min
            
            # Check for more possible meetings
            for p in people:
                from_loc = 'The Castro'
                to_loc = p['location']
                arrival_time = 540 + travel_times[from_loc][to_loc]
                avail_start = p['availability_start']
                avail_end = p['availability_end']
                required = p['required_time']
                
                earliest_start = max(arrival_time, avail_start)
                latest_start = avail_end - required
                
                if earliest_start <= latest_start:
                    if earliest_start >= current_end:
                        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, p))
    else:
        # This meeting can't be scheduled now, put it back into the queue
        heapq.heappush(priority_queue, (start_min, end_min, person))

# Convert the schedule to the required format
itinerary = []
for meeting in schedule:
    location = meeting['location']
    person = meeting['person']
    start = meeting['start_time']
    end = meeting['end_time']
    itinerary.append({
        'action': 'meet',
        'location': location,
        'person': person,
        'start_time': start,
        'end_time': end
    })

# Convert itinerary to JSON
import json
print(json.dumps({
    "itinerary": itinerary
}))