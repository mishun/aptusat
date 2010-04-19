#include <cassert>
#include <cstdio>
#include <vector>


const int N = 100000;

bool ok = true;
std::vector<int> impl[N];
int permval[N], tempval[N];
std::vector<int> unit;

int n, m;

bool propUnit(int x)
{
	if(permval[x] != 0)
	{
		if(permval[x] == 1)
			return true;
		else
		{
			ok = false;
			return false;
		}
	}

	permval[x] = 1;
	permval[x ^ 1] = -1;

	for(int i = 0; i < (int)impl[x].size(); i++)
		if(!propUnit(impl[x] [i]))
			return false;

	return true;
}

void tempPropUnit(int x)
{
	if(tempval[x] == -1)
	{
		propUnit(x);
		return;
	}

	tempval[x] = 1;
	tempval[x ^ 1] = -1;

	for(int i = 0; ok && i < (int)impl[x].size() && permval[x] == 0; i++)
	{
		int y = impl[x] [i];
		if(permval[y] == 0 && tempval[y] != 1)
			tempPropUnit(y);
	}
}

bool binSat()
{
	for(int i = 0; i < (int)unit.size(); i++)
		propUnit(unit[i]);

	for(int i = 0; ok && i < 2 * n; i++)
		if(permval[i] == 0 && tempval[i] == 0)
			tempPropUnit(i);

	return ok;
}


int main()
{
	freopen("input.txt", "r", stdin);
	freopen("output.txt", "w", stdout);

	scanf("%i %i", &n, &m);
	for(int i = 0; i < m; i++)
	{
		int a, b;
		scanf("%i %i", &a, &b);

		assert(a != 0);
		if(b == 0)
			b = a;
		else
		{
			int tmp;
			scanf("%i", &tmp);
			assert(tmp == 0);
		}

		if(a < 0)
			a = 2 * (-a - 1) + 1;
		else
			a = 2 * (a - 1);

		if(b < 0)
			b = 2 * (-b - 1) + 1;
		else
			b = 2 * (b - 1);

		if(a == b)
		{
			unit.push_back(a);
		}
		else
		{
			impl[a ^ 1].push_back(b);
			impl[b ^ 1].push_back(a);
		}
	}

	if(binSat())
	{
		printf("Yes\n");

		for(int i = 0; i < n; i++)
			if(permval[2 * i] == 1)
				printf("%i ", i + 1);
			else if(permval[2 * i] == 0 && tempval[2 * i] == 1)
				printf("%i ", i + 1);

		printf("0\n");
	}
	else
	{
		printf("No\n");
	}

	return 0;
}
