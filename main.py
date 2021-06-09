from sympy.logic.boolalg import integer_to_term, term_to_integer
from sympy.abc import x, y
from sympy.parsing.sympy_parser import parse_expr
from sympy.utilities.lambdify import lambdify, implemented_function
from sympy.logic.boolalg import Implies, Not
import random
from sympy import true, false
from itertools import combinations, compress

T0 = T1 = S = M = L = False


def save_zero(f, n):
    return calc(f, 0, n) == False


def save_one(f, n):
    return calc(f, 2**n - 1, n) == True


def self_dual(f, n):
    if (T0 and not T1) or (not T0 and T1):
        return False

    cur = 0  # текущий набор аргументов функции
    rev = 2 ** n - 1  # противоположный к текущему набор аргументов функции

    # проверка происходит, пока текущий набор меньше противоположного ему
    while cur < rev:
        # если значения функции на текущем и противоложном
        # наборе совпадают, функция не является самодвойственной
        if calc(f, cur, n) == calc(f, rev, n):
            return False

        cur += 1
        rev -= 1

    return True


def isPrecede(a, b):
    for i in range(0, len(a)):
        if a[i] == 1 and b[i] == 0:
            return False

    return True


def monotonic(f, n):
    vals = []  # динамический массив значений функции

    for cur in range(0, 2 ** n):
        vals.append(int(calc(f, cur, n) == True))

        i = 2
        # пробегаемся по степеням двойки, не больше текущей длины массива значений функции
        while i <= len(vals):
            # если текущий набор аргументов функции является степенью двойки i
            # и предпоследняя половина вектора значений функции длины i/2 не предшествует
            # последней половине, то функция не является монотонной
            if cur % i == i - 1 and not isPrecede(vals[-i:-i//2], vals[-i//2:]):
                return False
            i *= 2

        cur += 1

    return True


def i_m(f, n):
    cur = 0  # текущий набор аргументов функции
    fs = []  # динамический массив наборов аргументов, где функция истинна
    m = 2  # порядок класса замкнутости I

    while cur < 2 ** n:
        val = calc(f, cur, n)

        if val == True:
            fs.append(cur)

        # если число истинных значений функции не меньше двух
        # и не нашлось ни одной переменной, сохраняющей единицу
        # на любых двух наборах аргументов, то
        # функция не принадлежит рассматриваемому классу
        if len(fs) >= 2 and not check_list_1(fs, 2, n):
            return 1

        cur += 1

    # если число истинных значений функции меньше двух,
    # то функция не принадлежит рассматриваемому классу
    if len(fs) < 2:
        return 1

    # пробегаемся по возможным порядкам класса I,
    # начиная с двух и заканчивая числом истинных значений функции
    while m <= len(fs):
        if check_list_1(fs, m, n):
            # если очередная проверка на наличие в любых m наборах
            # переменной, принимающей на них единицу, прошла успешно,
            # то порядок увеличивается на единицу
            m += 1
        else:
            # если m не является порядком класса, то
            # итоговым порядком класса является m - 1
            return m - 1

    return m - 1


def o_m(f, n):
    fs = [] # динамический массив наборов аргументов, где функция истинна
    m = 2 # порядок класса замкнутости O

    for cur in range(0, 2 ** n):
        val = calc(f, cur, n)

        if val == False:
            fs.append(cur)

        # если число истинных значений функции не меньше двух
        # и не нашлось ни одной переменной, сохраняющей нуль
        # на любых двух наборах аргументов, то
        # функция не принадлежит рассматриваемому классу
        if len(fs) >= 2 and not check_list_0(fs, 2, n):
            return 1

    # если число истинных значений функции меньше двух,
    # то функция не принадлежит рассматриваемому классу
    if len(fs) < 2:
        return 1

    while m <= len(fs):
        if check_list_0(fs, m, n):
            # если очередная проверка на наличие в любых m наборах
            # переменной, принимающей на них нуль, прошла успешно,
            # то порядок увеличивается на единицу
            m += 1
        else:
            # если m не является порядком класса, то
            # итоговым порядком класса является m - 1
            return m - 1

    return m - 1


def check_list_0(fs, m, n):
    combs = combinations(fs, m)  # все возможные сочетания из наборов аргументов функции по m

    for el in combs:
        dis = 0
        for p in el:
            dis |= p

        # если в дизъюнкции m сочетаний наборов аргументов функции
        # не нашлось ни одного нуля, то m не является порядком класса I
        if 0 not in integer_to_term(dis, n):
            return False

    return True


def check_list_1(fs, m, n):
    combs = combinations(fs, m)  # все возможные сочетания из наборов аргументов функции по m

    t = 2 ** n - 1

    for el in combs:
        con = t
        for p in el:
            con &= p

        # если в конъюнкции m сочетаний наборов аргументов функции
        # не нашлось ни одной единицы, то m не является порядком класса I
        if 1 not in integer_to_term(con, n):
            return False

    return True


def o_inf(f, n):
    cur = 0  # текущий набор аргументов функции
    distinct = []  # список переменных, не удовлетворяющих условию замкнутости

    while cur < 2 ** n:
        val = calc(f, cur, n)
        for i in range(0, n):
            # если текущая рассматриваемая переменная
            # не находится в списке неудовлетворяющих,
            # данная переменная в текущем наборе равна единице,
            # а значение функции равно нулю, то
            # эта переменная не удовлетворяет условию замкнутости
            if i not in distinct and val == False and cur >> i & 1 == 1:
                distinct.append(i)
                # если число неудовлетворяющих переменных
                # стало равно равно числу переменных функци,
                # то функция не принадлежит рассматриваемому классу
                if len(distinct) == n:
                    return False
        cur += 1

    return True


def i_inf(f, n):
    cur = 0  # текущий набор аргументов функции
    distinct = []  # список переменных, не удовлетворяющих условию замкнутости

    while cur < 2 ** n:
        val = calc(f, cur, n)
        for i in range(0, n):
            # если текущая рассматриваемая переменная
            # не находится в списке неудовлетворяющих,
            # данная переменная в текущем наборе равна единице,
            # а значение функции равно нулю, то
            # эта переменная не удовлетворяет условию замкнутости
            if i not in distinct and val == True and cur >> i & 1 == 0:
                distinct.append(i)
                # если число неудовлетворяющих переменных
                # стало равно равно числу переменных функци,
                # то функция не принадлежит рассматриваемому классу
                if len(distinct) == n:
                    return False
        cur += 1

    return True


def u(f, n):
    cur = 0  # текущий набор аргументов функции
    t = [0] * n
    distinct = []

    while cur < 2 ** n:
        val = calc(f, cur, n)
        for i in range(0, n):
            if i not in distinct:
                if val == bool(cur >> i & 1):
                    t[i] += 1
                elif t[i] > 0 and val != bool(cur >> i & 1):
                    distinct.append(i)
                    if len(distinct) == n:
                        return False
        cur += 1
    return True


def linear(f, n):
    if n <= 10:
        # пробегаемся по всем наборам аргументов функции, начиная с тройки
        for x in range(3, 2**n):
            term = integer_to_term(x, n)
            ones = term.count(1)

            # набор только с одной единицей не интересует,
            # так как соответствующее слагаемое полинома
            # Жегалкина будет состоять из одной переменной
            if ones == 1:
                continue

            coef = 0  # коэффициент при соотвестующем слагаемом полинома Жегалкина
            for i in range(1, ones + 1):
                # находим все возможные сочетания индексов единиц по i
                combs = combinations(compress(range(0, n), term), i)
                for comb in combs:
                    # формируем сравнимый с рассматриваемым x
                    # набор аргументов, в котором единицы,
                    # стоящие на индексах из текущего сочетания, заменяются нулями
                    comp_set = [0 if ind in comb else bit for ind, bit in enumerate(term)]
                    coef ^= int(calc(f, term_to_integer(comp_set), n) == True)
            coef ^= int(calc(f, x, n) == True)

            # если в полиноме Жегалкина присутствует слагаемое
            # с более чем одним множителем, функция является нелинейной
            if coef == 1:
                return False

        return True
    else:
        a_0 = calc(f, 0, n)
        attempts = 5 * n

        for i in range(0, attempts):
            random_number = random.getrandbits(n)
            tmp = random_number
            f_x = int(calc(f, random_number, n) == True)
            random_number = random.getrandbits(n)
            f_y = int(calc(f, random_number, n) == True)
            f_x_y = int(calc(f, tmp ^ random_number, n) == True)

            if a_0 ^ f_x ^ f_y != f_x_y:
                return False

        return True


def calc(f, args, n):
    return f(*[true if x == 1 else false for x in integer_to_term(args, n)])


string = input("Введите логическое выражение: ")
expr = parse_expr(string)
variables = list(expr.atoms())
n = len(variables)

f = lambdify(variables, expr, modules=[{'Implies': Implies}, 'numpy'])

T0 = save_zero(f, n)
T1 = save_one(f, n)
S = self_dual(f, n)
M = monotonic(f, n)
L = linear(f, n)

print('Save 0: ', T0)
print('Save 1: ', T1)
print('Self dual: ', S)
print('Monotonic: ', M)
print('Linear: ', L)

m = o_m(f, n)
if m < 2:
    print('O^m: False')
else:
    print('O^m: m = ' + str(m))

m = i_m(f, n)
if m < 2:
    print('I^m: False')
else:
    print('I^m: m = ' + str(m))

print('O^inf: ', o_inf(f, n))
print('I^inf: ', i_inf(f, n))
print('U: ', u(f, n))
