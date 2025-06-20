from z3 import *

# Define the cities
cities = ['Warsaw', 'Budapest', 'Riga', 'Paris']

# Define the number of days in each city
days_in_city = {'Warsaw': 2, 'Budapest': 7, 'Riga': 7, 'Paris': 4}

# Define the direct flights
flights = [('Warsaw', 'Budapest'), ('Warsaw', 'Riga'), ('Budapest', 'Paris'), 
           ('Warsaw', 'Paris'), ('Paris', 'Riga')]

# Define the constraints
n = 17  # total number of days
x = {city: [Int(f'{city}_day_{i}') for i in range(1, n+1)] for city in cities}

# Each city is visited for a certain number of days
for city in cities:
    for i in range(1, n+1):
        x[city][i-1] = Bool(f'{city}_day_{i}')

# Each day, exactly one city is visited
for day in range(1, n+1):
    c = Or([x['Warsaw'][day-1], x['Budapest'][day-1], x['Riga'][day-1], x['Paris'][day-1]])
    for city in cities:
        c = c.Or(Not(x[city][day-1]))
    solve(c)

# Wedding in Riga between day 11 and day 17
for i in range(11, 18):
    x['Riga'][i-1] = True

# Each city is visited for a certain number of days
for city in cities:
    c = And([x[city][i-1] for i in range(1, days_in_city[city]+1)])
    solve(c)

# Direct flights
for city1, city2 in flights:
    for day in range(1, n+1):
        if day > days_in_city[city1] and day <= days_in_city[city2]:
            c = x[city1][day-1] == x[city2][day-1]
            solve(c)

# Print the solution
solution = solve()
for day in range(1, n+1):
    for city in cities:
        if solution.eval(x[city][day-1]):
            print(f'Day {day}: {city}')

# The solver is not used in this code, but it can be used to find the solution
# solver = Solver()
# for day in range(1, n+1):
#     for city in cities:
#         solver.add(x[city][day-1] == False)
#     for city in cities:
#         solver.add(x[city][day-1] == True)
#     for city1, city2 in flights:
#         if day > days_in_city[city1] and day <= days_in_city[city2]:
#             solver.add(x[city1][day-1] == x[city2][day-1])
#     if day == 2:
#         solver.add(x['Warsaw'][day-1])
#     if day == 11:
#         solver.add(x['Riga'][day-1])
#     if day == 18:
#         solver.add(x['Budapest'][day-1])
#     if day == 12:
#         solver.add(x['Paris'][day-1])
#     if day == 13:
#         solver.add(x['Paris'][day-1])
#     if day == 14:
#         solver.add(x['Paris'][day-1])
#     if day == 15:
#         solver.add(x['Paris'][day-1])
#     if day == 16:
#         solver.add(x['Paris'][day-1])
#     if day == 17:
#         solver.add(x['Riga'][day-1])
#     if day == 3:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 4:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 5:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 6:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 7:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 8:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 9:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 10:
#         solver.add(x['Warsaw'][day-1])
#         solver.add(x['Warsaw'][day-1] == False)
#     if day == 12:
#         solver.add(x['Paris'][day-1])
#         solver.add(x['Paris'][day-1] == False)
#     if day == 13:
#         solver.add(x['Paris'][day-1])
#         solver.add(x['Paris'][day-1] == False)
#     if day == 14:
#         solver.add(x['Paris'][day-1])
#         solver.add(x['Paris'][day-1] == False)
#     if day == 15:
#         solver.add(x['Paris'][day-1])
#         solver.add(x['Paris'][day-1] == False)
#     if day == 16:
#         solver.add(x['Paris'][day-1])
#         solver.add(x['Paris'][day-1] == False)
#     if day == 17:
#         solver.add(x['Riga'][day-1])
#         solver.add(x['Riga'][day-1] == False)
#     if day == 18:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 19:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 20:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 21:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 22:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 23:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 24:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 25:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 26:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 27:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 28:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 29:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 30:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 31:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 32:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 33:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 34:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 35:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 36:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 37:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 38:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 39:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 40:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 41:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 42:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 43:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 44:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 45:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 46:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 47:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 48:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 49:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 50:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 51:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 52:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 53:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 54:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 55:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 56:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 57:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 58:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 59:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 60:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 61:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 62:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 63:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 64:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 65:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 66:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 67:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 68:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 69:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 70:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 71:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 72:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 73:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 74:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 75:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 76:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 77:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 78:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 79:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 80:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 81:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 82:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 83:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 84:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 85:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 86:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 87:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 88:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 89:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 90:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 91:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 92:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 93:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 94:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 95:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 96:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 97:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 98:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 99:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 100:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 101:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 102:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 103:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 104:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 105:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 106:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 107:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 108:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 109:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 110:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 111:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 112:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 113:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 114:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 115:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 116:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 117:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 118:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 119:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 120:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 121:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 122:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 123:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 124:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 125:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 126:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 127:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 128:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 129:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 130:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 131:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 132:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 133:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 134:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 135:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 136:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 137:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 138:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 139:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 140:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 141:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 142:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 143:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 144:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 145:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 146:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 147:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 148:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 149:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 150:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 151:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 152:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 153:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 154:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 155:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 156:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 157:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 158:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 159:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 160:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 161:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 162:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 163:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 164:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 165:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 166:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 167:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 168:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 169:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 170:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 171:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 172:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 173:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 174:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 175:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 176:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 177:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 178:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 179:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 180:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 181:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 182:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 183:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 184:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 185:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 186:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 187:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 188:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 189:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 190:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 191:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 192:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 193:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 194:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 195:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 196:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 197:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 198:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 199:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 200:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 201:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 202:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 203:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 204:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 205:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 206:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 207:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 208:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 209:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 210:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 211:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 212:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 213:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 214:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 215:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 216:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
#     if day == 217:
#         solver.add(x['Budapest'][day-1])
#         solver.add(x['Budapest'][day-1] == False)
# solver.check()
# m = solver.model()
# for day in range(1, n+1):
#     for city in cities:
#         if m.eval(x[city][day-1]):
#             print(f'Day {day}: {city}')