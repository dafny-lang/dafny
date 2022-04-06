using System;
using Xunit;
using Dafny;

namespace DafnyRuntime.Tests {
  public class BigRationalTests {
    [Fact]
    public void FromDoubleZero() {
      var zeroBigRational1 = new BigRational(0);
      var zeroBigRational2 = new BigRational(0.0);
      Assert.Equal(zeroBigRational1, zeroBigRational2);
    }

    [Fact]
    public void FromDoubleNegZero() {
      var negZeroBigRational = new BigRational(-0.0);
      var zeroBigRational = new BigRational(0);
      Assert.Equal(zeroBigRational, negZeroBigRational);
    }

    private readonly (BigRational, Double)[] randomTests = {
      (new BigRational(927296365428443, 1125899906842624), 0.82360462043990434),
      (new BigRational(4447179682496439, 4503599627370496), 0.98747225563054797),
      (new BigRational(8426611987042531, 36028797018963968), 0.23388546618992398),
      (new BigRational(-6636107173280089, 144115188075855872), -0.046047243610348239),
      (new BigRational(3915364568927821, 562949953421312), 6.9550846307603482),
      (new BigRational(4597473216979439, 562949953421312), 8.1667529929408982),
      (new BigRational(2551337632173663, 4503599627370496), 0.56651075656636585),
      (new BigRational(4756054783734857, 4503599627370496), 1.0560563054562115),
      (new BigRational(5440540953349569, 144115188075855872), 0.037751336455154945),
      (new BigRational(-5203742103872157, 9007199254740992),-0.57773142979302217),
      (new BigRational(5723427281034493, 9007199254740992),0.63542807471722507),
      (new BigRational(-6389257191067805, 36028797018963968),-0.17733751109438325),
      (new BigRational(-8954711214129107, 18014398509481984),-0.49708632843976125),
      (new BigRational(-8347345265298179, 1125899906842624),-7.4139319264238592),
      (new BigRational(-4865558575878153, 9007199254740992),-0.54018551586023122),
      (new BigRational(4673897135318989, 4503599627370496),1.0378136428721405),
      (new BigRational(-8024722250936575, 288230376151711744),-0.027841348153786246),
      (new BigRational(-4560619626397081, 4503599627370496),-1.0126609831566837),
      (new BigRational(4184041432746541, 72057594037927936),0.058065239182760478),
      (new BigRational(6922249663345993, 72057594037927936),0.096065511980630749),
      (new BigRational(-4701546840996525, 9007199254740992),-0.52197655542280119),
      (new BigRational(-8976159437430157, 4503599627370496),-1.9931077760282705),
      (new BigRational(1939121425480651, 9007199254740992),0.21528572541125734),
      (new BigRational(-17977441348183, 17592186044416),-1.0218992286003754),
      (new BigRational(1104939973054919, 18014398509481984),0.061336489945713557),
      (new BigRational(820567855802739, 1125899906842624),0.72881066142359696),
      (new BigRational(-1987935766587255, 2251799813685248),-0.88282082381641258),
      (new BigRational(2492251144396307, 1125899906842624),2.2135636829257406),
      (new BigRational(1827958888279343, 2251799813685248),0.81177681833437232),
      (new BigRational(-5484033389941415, 36028797018963968),-0.15221250343315271),
      (new BigRational(-5289844312837451, 2251799813685248),-2.3491627811178311),
      (new BigRational(4913293101107683, 562949953421312),8.727761804130699),
      (new BigRational(-2948562119186421, 9007199254740992),-0.32735615542583096),
      (new BigRational(-6862347063504171, 9007199254740992),-0.76187357128711619),
      (new BigRational(1827572534090039, 1125899906842624),1.6232104852154441),
      (new BigRational(-8043655689920947, 18014398509481984),-0.4465125874553692),
      (new BigRational(-6308901275351155, 2251799813685248),-2.8017149823927467),
      (new BigRational(-7715867640875435, 72057594037927936),-0.10707917387325121),
      (new BigRational(-7341421037286571, 9007199254740992),-0.8150614669063051),
      (new BigRational(474554815513697, 281474976710656),1.6859573844161595),
      (new BigRational(7957863012409667, 9007199254740992),0.88350027431901201),
      (new BigRational(-1464477700666433, 9007199254740992),-0.16258968623299819),
      (new BigRational(-5566835050154875, 36028797018963968),-0.15451071117430701),
      (new BigRational(-709052063954143, 281474976710656),-2.5190589665916114),
      (new BigRational(-4787357441814319, 18014398509481984),-0.26575172295064226),
      (new BigRational(-6696300619422607, 1125899906842624),-5.9475097019957408),
      (new BigRational(-7412190823825045, 18014398509481984),-0.41145924577629361),
      (new BigRational(8864370755405419, 4503599627370496),1.9682857022929976),
      (new BigRational(7610886275072657, 9007199254740992),0.84497811803892564),
      (new BigRational(-3938916528258133, 4503599627370496),-0.87461516434975306),
      (new BigRational(-803303058030827, 1125899906842624),-0.71347644062209792),
      (new BigRational(-799443499002689, 1125899906842624),-0.71004846358374696),
      (new BigRational(7971159898256637, 9007199254740992),0.88497652520132386),
      (new BigRational(-6585879308818185, 1125899906842624),-5.8494358768418886),
      (new BigRational(1770024842854789, 1125899906842624),1.572097867756729),
      (new BigRational(1259611310808437, 1125899906842624),1.1187595834702408),
      (new BigRational(7959326368268927, 9007199254740992),0.88366273945582907),
      (new BigRational(8277468306835131, 4503599627370496),1.8379671799706745),
      (new BigRational(562633482211725, 9007199254740992),0.062464864637648554),
      (new BigRational(-8243384688676049, 2251799813685248),-3.660798192884251),
      (new BigRational(-5166267193134141, 2251799813685248),-2.2942835156732415),
      (new BigRational(5337582959869, 2199023255552),2.4272517111371599),
      (new BigRational(-2929646530058431, 36028797018963968),-0.081314025792101646),
      (new BigRational(336890525002427, 140737488355328),2.3937511528688091),
      (new BigRational(-3710970806650707, 18014398509481984),-0.20600026166277025),
      (new BigRational(-8780967036370177, 2251799813685248),-3.8995327129010779),
      (new BigRational(1335801057703783, 1125899906842624),1.1864296724651018),
      (new BigRational(1576771334859249, 281474976710656),5.601817089694979),
      (new BigRational(-72428812496465, 8796093022208),-8.2342026526549716),
      (new BigRational(4670753795521525, 9007199254740992),0.51855784061433374),
      (new BigRational(3405531723685621, 70368744177664),48.395516553307814),
      (new BigRational(7506843571026201, 9007199254740992),0.833427057481262),
      (new BigRational(-596272125527519, 1125899906842624),-0.52959603416226653),
      (new BigRational(6362760647712921, 4503599627370496),1.4128166742539519),
      (new BigRational(4849407370371105, 36028797018963968),0.13459809295932337),
      (new BigRational(-5331480999765141, 4503599627370496),-1.1838265922581617),
      (new BigRational(-2104448716421817, 4503599627370496),-0.4672814838228716),
      (new BigRational(7195562997508281, 36028797018963968),0.19971699287436254),
      (new BigRational(3101647305822055, 281474976710656),11.019264810208735),
      (new BigRational(1218753892703533, 562949953421312),2.1649418128495999),
      (new BigRational(6369294871587343, 9007199254740992),0.7071337817063198),
      (new BigRational(-5671706098754149, 36028797018963968),-0.15742146749359445),
      (new BigRational(6868939227670069, 562949953421312),12.201687176496401),
      (new BigRational(-672803910403677, 562949953421312),-1.195139827820805),
      (new BigRational(-4519033402066533, 2251799813685248),-2.006853972809767),
      (new BigRational(1161336276022567, 2251799813685248),0.515736909189076),
      (new BigRational(-1479182120758195, 2251799813685248),-0.65688881923184672),
      (new BigRational(1913519632600293, 2251799813685248),0.84977342167404624),
      (new BigRational(2375030178315213, 1125899906842624),2.1094505505161125),
      (new BigRational(8679438564835755, 9007199254740992),0.96361125355001798),
      (new BigRational(5194343902086335, 2251799813685248),2.3067520791670115),
      (new BigRational(2883379566302685, 4503599627370496),0.64023887664858781),
      (new BigRational(-2668445486650393, 18014398509481984),-0.14812848096181735),
      (new BigRational(2041905164676459, 9007199254740992),0.22669701279248267),
      (new BigRational(6241403994498935, 9007199254740992),0.69293504206801415),
      (new BigRational(-8371100538584825, 4503599627370496),-1.8587577118777843),
      (new BigRational(-3804035542556243, 2251799813685248),-1.6893311383353562),
      (new BigRational(-2863846728632385, 9007199254740992),-0.31795085771251064),
      (new BigRational(1983948363857061, 2251799813685248),0.88105006128860675),
      (new BigRational(-2003460171926341, 2251799813685248),-0.88971504471683938),
      (new BigRational(1, 1024), 0.0009765625),
      (new BigRational(4503599681057587, 4294967296), 1048576.0125),
    };

    private readonly (BigRational, Double)[] badTests = {
      (new BigRational(-2003460171926342, 2251799813685248),-0.88971504471683938)
    };

    [Fact]
    public void FromDoubleRandom() {
      foreach (var (expectedBigRational, dbl) in randomTests) {
        var actualBigRational = new BigRational(dbl);
        Assert.Equal(expectedBigRational, actualBigRational);
      }
    }

    [Fact]
    public void FromDoubleRandomBad() {
      foreach (var (expectedBigRational, dbl) in badTests) {
        var actualBigRational = new BigRational(dbl);
        Assert.NotEqual(expectedBigRational, actualBigRational);
      }
    }
  }
}
